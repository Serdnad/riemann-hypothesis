module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle035
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle183
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthOfAvTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle818
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle800
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle801
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle071
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle799
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle319
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle827
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle813
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle808
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInner
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle283
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle266
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle281
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle282
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle278
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle269
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle157
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.mem_j_iff_umax_and_chi_eq_one_of_split_out : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hMI : MtInput D M tp.tup C.Q) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → ∀ κ : GAf D.host.E D.R.nV, TrivOutside {s.v} κ → (κ ∈ (mlX M X i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ h : κ ∈ (mlX M X i).J, (mlX M X i).χ ⟨κ, h⟩ = 1 := by
  first | exact @_root_.GlobalTheory.LocLevel.level_at_splitOut_alt | exact _root_.GlobalTheory.LocLevel.level_at_splitOut_alt | (intros; apply _root_.GlobalTheory.LocLevel.level_at_splitOut_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ThetaExh
theorem typeOrth_of_pin_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, MtForm D P.M i → GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := by
  intro hL D P i hF
  obtain ⟨B, hB, hinner⟩ := hF
  exact GlobalTheory.ThetaExh.typeOrth_of_avTied D P.M P.H.av i B hB hinner
    (GlobalTheory.AlgFormsFin.finiteDimensional_forms D D.R.nV (P.M.loc i).wt (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel D.host.E D.R.nV))
end GlobalTheory.ThetaExh
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.CoefDuty.LargeRing
theorem evO_laws_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (P₁ P₂ : D7 → Prop), (_root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₂ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup fun D' => P₁ D' ∧ P₂ D') ∧ ((∀ D', P₁ D' → P₂ D') → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₂) ∧ (_root_.GlobalTheory.CoefDuty.AutomorphicSideExists A M C tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ), ∃ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big₀ w ⊆ big w) ∧ _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L ∧ P₁ (withLoc L)) ∧ ∀ (big big' : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big w ⊆ big' w) → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big' L → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L := by
  classical
  intro D cf jE A M C tup P₁ P₂
  have anti : ∀ (big big' : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big w ⊆ big' w) →
      _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big' L → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L := by
    intro big big' L h hL
    obtain ⟨Sp, hA, hs⟩ := hL
    exact ⟨{ Sp with iq_big := fun i z hz => Sp.iq_big i z (h _ hz) }, hA, hs⟩
  refine ⟨?_, ?_, ?_, anti⟩
  · rintro ⟨b, hb⟩ ⟨c, hc⟩
    exact ⟨fun w => b w ∪ c w, fun L hL => ⟨hb L (anti _ _ L (fun _ => Finset.subset_union_left) hL),
      hc L (anti _ _ L (fun _ => Finset.subset_union_right) hL)⟩⟩
  · rintro h ⟨b, hb⟩
    exact ⟨b, fun L hL => h _ (hb L hL)⟩
  · rintro hE ⟨b, hb⟩ big₀
    obtain ⟨L, hL⟩ := hE fun w => big₀ w ∪ b w
    exact ⟨fun w => big₀ w ∪ b w, L, fun _ => Finset.subset_union_left, hL,
      hb L (anti _ _ L (fun _ => Finset.subset_union_right) hL)⟩
end GlobalTheory.CoefDuty.LargeRing
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory.TieInePolyPin
theorem inePol_eq_wdAt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) r) w) σ = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol σ := by
  intro hL D P i w hw m r hc hpst σ hσ
  have hc' : Continuous (fun g => ((GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w g : GL _ _) : Matrix (Fin m) (Fin m) (Om (D.nd.l i)))) :=
    ((hc.matrix_map (GlobalTheory.T.continuous_iotaOQ' D.nd D.naut i)).comp continuous_subtype_val)
  rw [(P.wdOf i m (mapRep (iotaOQ D.nd D.naut i) r) w).1, P.T.inePol w _ σ hσ]
  obtain ⟨LL, Bw, hj, e2⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) (mapRep (iotaOQ D.nd D.naut i) r) w hw
  rw [e2]
  refine congrArg (fun x => GlobalTheory.WeilDeligne.WD.inePol x σ) ?_
  exact GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩
    (D.naut.iotaQC i) D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _ Bw (D.nbr i w hw) (D.nd.plOm.2 w) hj (D.nbr_ind i w hw) m _ hc'
    (GlobalTheory.T.isPotSemistable_independent_of_inducingEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ D.host.E D.nd.Om (D.nd.plOm.1 w) _ _
      (D.nbr i w hw) Bw (D.nbr_ind i w hw) hj m _ hc' hpst) hpst
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.Pass.TieInePoly D := by
  intro hL D P i w hw K' h hN hF hS m r hc hpot σ hσ p hp d hd
  exact GlobalTheory.T.inertiaPolynomial_kills_potentiallyCrystalline_module D i w hw K' h hN hF hS m r hc hpot σ hσ p
    (hp.trans (_root_.GlobalTheory.TieInePolyPin.inePol_eq_wdAt_alt hL D P i w hw m r hc (GlobalTheory.T.potSemistable_of_potCrystalline_decompositionGroup D i w hw K' h hN hF hS m r hc hpot) σ hσ)) d hd
end GlobalTheory.TieInePolyPin
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LiftOther
end GlobalTheory.LiftOther
namespace GlobalTheory.LiftOther
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ L : G0g D.nd → GAf D.host.E D.R.nV, IsTypeGroupBlockLift D D.R.nV L → ∀ F ∈ D.naut.typeV i PI, ∀ (h : GL (Fin D.R.r) (ZMod (D.host.g k))) (g : G0g D.nd), g ⟨k, v⟩ = h → (∀ kv, kv ≠ ⟨k, v⟩ → g kv = 1) → ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧ IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧ NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := by
  intro hL D P i PI k v s hs c hc hcs L hLift F hF h g hg1 hg2
  classical
  obtain ⟨x, hxT, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s (s.loc D.R.nV (L g))
  refine ⟨x, hxT, ?_, ?_⟩
  · rw [hxe]
    have := ((hLift g).2 ⟨k, v⟩ s hs)
    rw [hg1] at this
    exact isLiftN_map' s c hc hcs _ _ h _ this
  obtain ⟨hj1, hj2⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  let K : Subgroup (GAf D.host.E D.R.nV) := (P.M.loc i).χ.ker.map (P.M.loc i).J.subtype
  set y := x⁻¹ * L g with hy
  have hsv : s.v ∈ PendOf.gPl D := ⟨⟨k, v⟩, by rw [← hs]; exact s.w_under⟩
  have hfin := gPl_finite D
  let T := hfin.toFinset.erase s.v
  have hyT : TrivOutside (T : Set _) y := by
    intro w hw
    rw [map_inv_mul]
    by_cases hws : w = s.v
    · subst hws
      rw [GlobalTheory.T.splitPlace_component_unitaryAdelic_determined s (L g) x hxe.symm]
      exact map_inv_mul_self _ x
    · have hwg : w ∉ PendOf.gPl D := by
        intro hwg; apply hw; simp [T, hws, hwg]
      rw [(hLift g).1 w hwg]
      have hx1 := hxT w (by simpa using hws)
      have e := map_inv_mul_self w x
      rw [hx1, mul_one] at e
      rw [e, mul_one]
  have hyK : y ∈ K := by
    refine GlobalTheory.T.mem_subgroup_of_trivOutside_of_local_points K T y hyT fun w hw => ?_
    have hwne : w ≠ s.v := (Finset.mem_erase.1 hw).1
    have hwg : w ∈ PendOf.gPl D := hfin.mem_toFinset.1 (Finset.mem_erase.1 hw).2
    obtain ⟨kv, hkv⟩ := hwg
    obtain ⟨s', hs'⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D kv
    have hs'v : s'.v = w := over_eq s' (by rw [hs']; exact hkv)
    have hkvne : kv ≠ ⟨k, v⟩ := by
      rintro rfl
      apply hwne
      rw [← hs'v]
      exact over_eq s' (by rw [hs', ← hs]; exact s.w_under)
    obtain ⟨p, hpT, hpe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s' (s'.loc D.R.nV y)
    have hloc : s'.loc D.R.nV y = s'.loc D.R.nV (L g) := by
      rw [hy, map_mul]
      have : s'.loc D.R.nV x⁻¹ = 1 := by
        rw [map_inv]
        rw [loc_eq_one_of_compAt' s' x (hxT _ (by rw [hs'v]; simpa using hwne)), inv_one]
      rw [this, one_mul]
    have hlift := (hLift g).2 kv s' hs'
    rw [hg2 kv hkvne, ← hloc, ← hpe] at hlift
    obtain ⟨ψ₀, ξ, hψ, -, hU⟩ := P.H.level.uni i j hj kv.1 kv.2 s' hs'
    obtain ⟨hpJ, hpχ⟩ := GlobalTheory.T.blockLiftIdentity_mem_unipotentLevel_character_one (P.M.loc i).J (P.M.loc i).χ s' D.R.r (D.host.g kv.1) (D.host.g_prime kv.1).one_lt
      ψ₀ ξ hψ hU p hpT hlift
    refine ⟨p, ⟨⟨p, hpJ⟩, hpχ, rfl⟩, hs'v ▸ hpT, ?_⟩
    rw [← hs'v]
    exact GlobalTheory.T.splitPlace_component_unitaryAdelic_determined s' p y hpe
  obtain ⟨⟨y', hy'J⟩, hy'χ, hy'e⟩ := hyK
  have hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hfix : NG.rt D.host.E D.R.nV y ((P.M.loc i).real F) = (P.M.loc i).real F := by
    have e := hTS.2 ⟨y', hy'J⟩
    have h1 : (((P.M.loc i).χ ⟨y', hy'J⟩ : ℂˣ) : ℂ) = 1 := by
      rw [show (P.M.loc i).χ ⟨y', hy'J⟩ = 1 from hy'χ]; rfl
    rw [h1, one_smul] at e
    have hy'y : y' = y := hy'e
    rw [← hy'y]; exact e
  have hLg : L g = x * y := by rw [hy, mul_inv_cancel_left]
  rw [hLg]
  funext z
  have e := congrFun hfix (z * x)
  simp only [NG.rt, LinearMap.coe_mk, AddHom.coe_mk] at e ⊢
  rw [← mul_assoc, e]
end GlobalTheory.LiftOther
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.MuUnrTie
theorem main_alt_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    GlobalTheory.HubX.MuUnr D := by
  intro _ hL D P i hl w hw
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.zero_lt_one) hj.2⟩
  have hjj : j.1 + 1 = D.nd.j i := Nat.sub_add_cancel hj.1
  have hlp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  rw [P.chr.unr_iff, P.chr.tw, P.chr.muC i j hjj, P.chr.etaTinv]
  refine GlobalTheory.MuTameQS.unrAt_mul ?_ (unrAt_inv (P.cf.isEta.unr w))
  unfold TupTied.tup
  refine GlobalTheory.MuTameQS.unrAt_mul ?_ ?_
  · refine (P.cf.isMu0 j).unr w fun k hk => ?_
    have e := eq_of_over_two hlp (D.host.g_prime k) w hw hk
    apply hl
    rw [e]
    fin_cases k <;> simp [TwistedPlaces.gset]
  · rw [D.nd.mu_w i, P.tp.xi_tw, D.nd.w_l i]
    refine GlobalTheory.MuTameQS.unrAt_mul ?_ ?_
    · unfold CharFrame.delAt
      split_ifs with h
      · refine P.cf.isDel'.unr w fun ho => D.host.pde_ne ?_
        rw [← h]
        exact eq_of_over_two hlp D.host.pde'_prime w hw ho
      · refine P.cf.isDel.unr w fun ho => h ?_
        exact eq_of_over_two hlp D.host.pde_prime w hw ho
    · have hpsi := P.tp.psi_is (D.nd.w i) (D.nd.w_tw i)
      rw [D.nd.w_l i, ← P.Q_eq i] at hpsi
      exact (hpsi.ram w).2 fun hq => D.nd.SQ_l i w (Or.inr hq) hw
end GlobalTheory.MuUnrTie
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TypeBlockConj
end GlobalTheory.TypeBlockConj
namespace GlobalTheory.TypeBlockConj

theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = GlobalTheory.DimPartsCompare.cPl (D.naut.plGw k v) → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  intro hL D P S hS i k v s hw hs hμt c hc hcs Q
  obtain ⟨hj1, hj2⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hconj : IsConjPl D.host (D.naut.plGw k v) s.w := by
    rw [hs]; exact GlobalTheory.DimPartsCompare.isConjPl_cPl _
  obtain ⟨hw₀, hi₀⟩ := GlobalTheory.T.conjugateSplitPlace_eq_conjugatePlace_and_embedding D s _ hconj
  obtain ⟨ψ₀, ξ, hψ, hξ, hU⟩ := P.H.level.uni i j hj k v (GlobalTheory.TypeTame.conjSP s) hw₀
  have hcc : ∀ x : D.host.E, D.host.conj (D.host.conj x) = x := fun x => by
    letI := Formalism.BasicNotions.Host.cmStar D.host
    rw [← GlobalTheory.DimPartsCompare.star_conj, ← GlobalTheory.DimPartsCompare.star_conj, star_star]
  have hcsd : IsCSD D.host (P.tp.tup (D.nd.mu i) j) := by
    have := (P.chr.csd _).1 (D.naut.muC_csd i)
    rwa [P.chr.muC i j hj] at this
  have hconj' : IsConjPl D.host s.w (D.naut.plGw k v) := by
    have := GlobalTheory.DimPartsCompare.isConjPl_cPl (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw k v))
    rwa [GlobalTheory.DimPartsCompare.cPl_cPl, ← hs] at this
  have hμ := hS.mu i s.w hw j hj
  have hrel : ∀ u, ξ⁻¹ u = (S i s.w hw).mu (Units.map c.toMonoidHom u) := by
    refine GlobalTheory.T.splitPlace_unitsCharacter_eq_of_agree_on_field s c hc hcs _ _ hμ.1 ?_ ?_
    · obtain ⟨N, hN⟩ := hξ.1
      exact ⟨N, fun u hu => by rw [MonoidHom.inv_apply, hN u hu, inv_one]⟩
    · intro x
      have e1 : Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) x =
          Units.map ((GlobalTheory.TypeTame.conjSP s).i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E))
            (Units.map (MonoidHomClass.toMonoidHom D.host.conj) x) := by
        ext
        simp [hi₀]
        change _ = (s.i (D.host.conj (D.host.conj (x : D.host.E)))).toCompletion
        rw [hcc]
      rw [MonoidHom.inv_apply, e1, hξ.2, hw₀, hcsd.1 _ _ hconj' x, inv_inv, hμ.2]
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (maximalRealSubfield D.host.E) s.v
  set ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E) := (π : s.v.adicCompletion (maximalRealSubfield D.host.E)) with hϖdef
  have hϖ : Valued.v ϖ = WithZero.exp (-1) := by
    rw [hϖdef, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  let d : GL (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)) :=
    ⟨Matrix.diagonal (fun a : Fin D.R.nV => if (a : ℕ) < D.R.r then 1 else ϖ),
     Matrix.diagonal (fun a : Fin D.R.nV => if (a : ℕ) < D.R.r then 1 else ϖ⁻¹),
     by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext a; split_ifs <;> simp [hϖ0],
     by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext a; split_ifs <;> simp [hϖ0]⟩
  obtain ⟨y, hyT, hyd⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV (GlobalTheory.TypeTame.conjSP s) d⁻¹
  obtain ⟨y0, hy0, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
  set f₀ := (P.M.loc i).real y0 with hf₀
  have hf0iso : f₀ ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    rw [P.H.av.typeV] at hy0; exact hy0
  have hf0type : f₀ ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hf0ne : f₀ ≠ 0 := fun h0 => hy00 ((P.M.loc i).real_inj (h0.trans (map_zero _).symm))
  refine ⟨NG.rt D.host.E D.R.nV y f₀, GlobalTheory.CompRed.isoTyp_stable _ _ _ hf0iso, ?_, ?_⟩
  · intro h0
    apply hf0ne
    funext g
    have := congrFun h0 (g * y⁻¹)
    simpa [NG.rt] using this
  · intro x hxT hxB
    have hv := GlobalTheory.T.splitPlace_completionIso_preserves_valuation s c hc hcs
    have hab := GlobalTheory.T.conjugateSplitPlace_unitaryLoc_eq_transpose_inv D.R.nV s x
    obtain ⟨κ, hκ⟩ : ∃ κ : GAf D.host.E D.R.nV, κ = y⁻¹ * x * y := ⟨_, rfl⟩
    have hκT : TrivOutside {s.v} κ := hκ ▸ GlobalTheory.TypeBlockConj.trivOutside_mul (GlobalTheory.TypeBlockConj.trivOutside_mul (GlobalTheory.TypeBlockConj.trivOutside_inv hyT) hxT) hyT
    have hκloc : (GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ = d * (GlobalTheory.TypeTame.conjSP s).loc D.R.nV x * d⁻¹ := by
      rw [hκ, map_mul, map_mul, map_inv, hyd, inv_inv]
    obtain ⟨hUni, hsup⟩ := GlobalTheory.T.diagUniformiserConj_transposeInv_mem_upperParahoric s D.R.r D.R.t c hv (s.loc D.R.nV x) ((GlobalTheory.TypeTame.conjSP s).loc D.R.nV x) hab hxB ϖ hϖ d rfl
    obtain ⟨u, hu, hbc⟩ := GlobalTheory.T.blockCharacter_eq_inv_at_transposeInv_lowerBlockDet s D.R.r D.R.t c hv (s.loc D.R.nV x) ((GlobalTheory.TypeTame.conjSP s).loc D.R.nV x) hab hxB ϖ hϖ d rfl
    have hκJ : κ ∈ (P.M.loc i).J := (hU.mem κ hκT).2 (by rw [hκloc]; exact hUni)
    have hchr := hU.chr κ hκJ hκT u (by rw [hu, hκloc]; rfl)
    rw [hψ.1 _ (by rw [hκloc]; exact hsup), one_mul] at hchr
    have hty := hf0type.2 ⟨κ, hκJ⟩
    have hval : blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) =
        (((P.M.loc i).χ ⟨κ, hκJ⟩ : ℂˣ) : ℂ) := by
      rw [hbc _ hμt, hchr, ← hrel u, MonoidHom.inv_apply, inv_inv]
    rw [hval]
    funext g
    have e := congrFun hty (g * y)
    have e2 : g * y * κ = g * x * y := by rw [hκ]; group
    rw [GlobalTheory.TypeBlockConj.rt_rt, Pi.smul_apply, ← e2]
    exact e
end GlobalTheory.TypeBlockConj
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RowUnitProof
end GlobalTheory.RowUnitProof
namespace GlobalTheory.RowUnitProof
theorem rowUnit_of_isTrue_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → RowUnit S := by
  intro hL D P hX S hS i w hw σ hσ
  obtain ⟨X⟩ := hX i
  obtain ⟨s, rfl⟩ := exists_splitPlace_eq D w hw
  have hB00 : X.B 0 0 = 0 := by
    have h := X.lin 0 X.C.zero_mem 0 X.C.zero_mem 0 X.C.zero_mem 1
    rw [one_smul, add_zero, one_mul] at h
    linear_combination -h
  have hne : Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (P.rep σ) ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
    have hmem := (X.isot σ y).1 hy
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    apply hy0
    have h := X.φ_inner y y
    rw [hmem, hB00] at h
    exact inner_self_eq_zero.1 h
  obtain ⟨B', hlin, hherm, hpos, hinv⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r X.A X.ρ X.C X.B X.lin X.herm
    X.pos X.stab X.inv (P.rep σ) hne
  obtain ⟨ι, T, -, -, hTinj, hTS, hTeq⟩ := hS.row i s hw σ hσ
  have hadd : ∀ x y z, B' x (y + z) = B' x y + B' x z := fun x y z => by
    simpa using hlin x y z 1
  have h0 : ∀ x, B' x 0 = 0 := fun x => by
    have h := hadd x 0 0
    rw [add_zero] at h
    linear_combination -h
  have hsmul : ∀ x (c : ℂ) y, B' x (c • y) = c * B' x y := fun x c y => by
    simpa [h0] using hlin x 0 y c
  have hadd' : ∀ x y z, B' (x + y) z = B' x z + B' y z := fun x y z => by
    rw [hherm, hadd, map_add (f := _), ← hherm, ← hherm]
  have hsmul' : ∀ (c : ℂ) x y, B' (c • x) y = starRingEnd ℂ c * B' x y := fun c x y => by
    rw [hherm, hsmul, map_mul, ← hherm]
  let Tm := LinearMap.codRestrict (P.rep σ).S T hTS
  have hTm : ∀ a, ((Tm a : (P.rep σ).S) : GAf D.host.E D.R.r → ℂ) = T a := fun _ => rfl
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v u => B' (Tm u) (Tm v))
    (fun _ _ _ => by simp only [map_add (f := _), hadd]) (fun _ _ _ => by simp only [map_smul, hsmul, smul_eq_mul, RingHom.id_apply])
    (fun _ _ _ => by simp only [map_add (f := _), hadd']) (fun _ _ _ => by simp only [map_smul, hsmul', smul_eq_mul]), ?_, ?_, ?_⟩
  · intro v u
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hherm _ _
  · intro v hv
    simp only [LinearMap.mk₂'ₛₗ_apply]
    refine hpos _ fun h => hv (hTinj ?_)
    rw [map_zero]
    exact congrArg Subtype.val h
  · intro g v u
    simp only [LinearMap.mk₂'ₛₗ_apply]
    obtain ⟨x, ⟨hx, hxg⟩, -⟩ := (GlobalTheory.SplitAdelic.main D.host.E D.R.r s).2.2
      (Matrix.GeneralLinearGroup.map ι.symm.toRingHom g)
    have hg : Matrix.GeneralLinearGroup.map ι.toRingHom (s.loc D.R.r x) = g := by
      rw [hxg]
      exact Units.ext (Matrix.ext fun a b => ι.apply_symm_apply _)
    have key : ∀ a, T (((S i s.w hw).row σ).π g a) = NG.rt D.host.E D.R.r x (T a) := fun a => by
      have := hTeq x hx a
      rw [hg] at this
      exact this
    exact hinv x (Tm u) (Tm v) _ _ (key u) (key v)
end GlobalTheory.RowUnitProof
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.NPin
theorem heckeStdTw_cover_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), HeckeStdTw P.H.cover.B :=
  fun _ D P =>
    Formalism.L2.heckeStd_of_plain P.H.cover GlobalTheory.HeckeStdFacts.heckeStdPlain P.H.hecke (GlobalTheory.SplitConjPlace.splitEx_all D)
      (Formalism.L2.genOutBad_of P.H.cover)
end GlobalTheory.NPin
end
end
