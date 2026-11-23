module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle245
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle018
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle417
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle694
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle547
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoMonodromyOfInertiaSeparableCharpoly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle829
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle236
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle019
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle239
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
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

@[expose] public section

section



section
section
section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
section Loc
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitRead GlobalTheory.PendOf ValuativeRel GlobalTheory.StepData
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory GlobalTheory.RegType
variable {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {w : HeightOneSpectrum (𝓞 E)}
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc) (hDZ : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt)
  (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L)
  {t : G E Ω} (ht : t ∈ Ine (F := E) A) (hκ : Formalism.L2.NT.TameCoupled A κ t L.gen)
include hi hrc hDZ ht hκ
end Loc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne in
theorem regLoc_of_greenLab : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D), GreenLab Γ → _root_.GlobalTheory.PendOf.RegularLocalCondition hL D := by
  intro hP hDZ hL D Γ hG k v π ρ f hρ hsq ⟨x, hx, hnk⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
  have hrc := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hw := D.naut.plGw_over k v
  have hA := GlobalTheory.RegType.allLab (Γ.O k) (hG k)
  have h5 := GlobalTheory.SerSys.Bridge.five_le D k
  have hx' := GlobalTheory.RegType.mem_principalCongruenceFixed_of_levelOne hw (I.i k v) (I.cont k v) π.π hx
  have hz := GlobalTheory.RegType.actK_ne_of_notKilled hw (I.i k v) (I.cont k v) π.π hx _ hnk
  have he := GlobalTheory.RegType.eSerC_mul_zIdem (Γ.O k) (hG k) ρ hρ.1 f (by rw [← Γ.eSer_def k f]; exact hρ.2)
  have hHas := GlobalTheory.RegType.has_of_actK (GlobalTheory.RegType.sysOf _ h5 hA) _ hx' hz he
  have hine : (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) D.R.r π).inePol (D.ntypes.tg k v) =
      ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod :=
    _root_.DiscreteGroups.sglob.DzType.Rt.inePol_eq_liftPoly_of_has (I.i k v) (I.cont k v) hrc hDZ (Γ.kv k v) _ h5 hA (D.ntypes.tg_mem k v)
      (Γ.tg_tame k v) hP.bz hP.geo π (DiscreteGroups.sglob.DzType.sixteen_sq_lt_g D k) f hHas
  refine ⟨WD.noMonodromy_of_inertia_separable_charpoly _ _ _ _ _ _ _ (D.ntypes.tg_mem k v) ?_, ?_⟩
  · rw [hine]
    exact GlobalTheory.GoodRowMono.separable_prod_teich _ (D.ntypes.teichC_inj k) hsq
  · have hSet : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
      .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
        (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
    have htame : (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) D.R.r π).tame := by
      first | (have hOpn := UpperTheory.One.M.opn _ (hrc); obtain ⟨a, ha, ε, hl⟩ := hOpn) | obtain ⟨a, ha, ε, -, hl⟩ := hrc
      refine GlobalTheory.SerSys.LabDepth.tame_of_isTameWD ((fun hx => haveI := UpperTheory.One.M.charZero_compl (D.naut.plGw k v); _root_.UpperTheory.One.M.LawsM.depth hl _ (UpperTheory.One.M.good_of_fixed ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩ _ hx) hx : _ → _) ?_)
      refine GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep π.toIrrRep).some.symm ?_
      refine (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => hx u fun a b => ?_, fun h0 => hz ?_⟩
      · have := GlobalTheory.StepData.mem_KOne.1 hu a b
        rwa [Matrix.sub_apply, Matrix.one_apply] at this
      · rw [h0, map_zero]
    have e1 : (Formalism.CyclotomicNorms.rootsBar f).map (fun x => X - C (D.ntypes.teichC k x)) =
        ((Formalism.CyclotomicNorms.rootsBar f).map (D.ntypes.teichC k)).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [_root_.GlobalTheory.PendOf.localLabelPolynomial, WD.lab_eq_iff_of_tame hSet htame, hine, e1, roots_multiset_prod_X_sub_C]
    exact ⟨GlobalTheory.SerSys.TameGen.Has.monic hHas, rfl⟩
end DiscreteGroups.sglob.DzType.Rt
end
end
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabFixed
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
theorem labLP_twist_eq_labAt_ofDet : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (s : ℝ), D.naut.items₂ k (D.naut.plGw k v) (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (D.naut.plGw k v)) s) = _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) := by
  intro hPr hL D P S hT i k v hw hχ s
  haveI := host_isCMField D.host
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, (j : ℕ) + 1 = D.nd.j i := by
    have := D.nd.j_range i
    exact ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  have hμ : IsComp (P.tp.tup (D.nd.mu i) j) (D.naut.plGw k v) (S i _ hw).mu := hT.mu i _ hw j hj
  have hψ : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹ := by
    rw [P.chr.tw, P.chr.muC i j hj, P.chr.etaTinv]
  have hc : IsComp (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 (D.naut.plGw k v)
      ((P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v)) := by
    rw [hψ]; exact ⟨ParLaws.isSmoothChar_loc _ _, fun x => rfl⟩
  rw [P.lab k v, P.T.tw, WD.lab_lpTw, _root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp hPr.fin hL D P _ _ _ hc, _root_.GlobalTheory.PendOf.localLabelPolynomial]
  have hηs : IsSmoothChar (P.cf.eta.loc (D.naut.plGw k v))⁻¹ := by
    have := ParLaws.isSmoothChar_loc (P.cf.eta⁻¹) (D.naut.plGw k v)
    convert this using 1
    exact MonoidHom.ext fun x => rfl
  have hu : ∀ x, Formalism.L2.Host.IsUnitAt (D.naut.plGw k v) x → (P.cf.eta.loc (D.naut.plGw k v))⁻¹ x = 1 := by
    intro x hx
    rw [MonoidHom.inv_apply, P.cf.isEta.unr _ x hx, inv_one]
  have e : (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v) =
      (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ := by
    rw [GlobalTheory.Published.ParamAboveModel.eq_loc hμ]
    rfl
  have key : ∀ (ξ' : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ →* ℂˣ) (h' : IsSmoothChar ξ'),
      ξ' = (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ →
      WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 ξ' h')) =
        WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 (S i _ hw).mu hχ)) := by
    rintro _ h' rfl
    exact _root_.GlobalTheory.LabFixed.lab_rcAt_ofDet_mul_eq hL D k v _ _ hχ hηs hu h'
  exact key _ _ e
end GlobalTheory.LabFixed
end
end
end
