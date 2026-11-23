module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle050
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle281
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle285
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle278
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle260
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle258
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle253
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.LocEigAgree
theorem main_alt_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q Q' : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite → (∀ σ σ', IsLocS (P.H.av.S i Q) sp σ → IsLocS (P.H.av.S i Q') sp σ' → GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ') → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → ∀ F' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q'), F' ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F' ≠ 0 → ∀ c c' : ℂ, NG.heckeD (P.M.loc i).J Ds F = c • F → NG.heckeD (P.M.loc i).J Ds F' = c' • F' → c = c' := by
  intro _hAF hL D P i Q Q' sp hJ Ds hDs hbi hfin hcls F hF hFT hF0 F' hF' hF'T hF'0 c c' hc hc'
  classical
  have hK : ∀ f ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ,
      ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ f = f := by
    intro f hf κ hκ
    obtain ⟨h1, h2⟩ := hJ κ hκ.2
    have hJκ : κ ∈ (P.M.loc i).J := h1.2 hκ.1
    have e := hf.2 ⟨κ, hJκ⟩
    rw [h2 hJκ] at e
    simpa using e
  have hJU : ∀ x ∈ Ds, ∀ x' ∈ Ds, (x⁻¹ * x' ∈ (P.M.loc i).J ↔ x⁻¹ * x' ∈ Umax D.host.E D.R.nV) :=
    fun x hx x' hx' => (hJ _ (GlobalTheory.HeckeScalarAll.trivOutside_mul (GlobalTheory.HeckeScalarAll.trivOutside_inv (hDs x hx))
      (hDs x' hx'))).1
  have hfinU : ((fun x : GAf D.host.E D.R.nV => (x : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV)) '' Ds).Finite := by
    let φ : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J → GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV := fun c =>
      if hc : ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c then (hc.choose : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV) else ((1 : GAf D.host.E D.R.nV) : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV)
    refine (hfin.image φ).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    have hc : ∃ y ∈ Ds, (y : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) := ⟨x, hx, rfl⟩
    refine ⟨(x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J), ⟨x, hx, rfl⟩, ?_⟩
    simp only [φ, dif_pos hc]
    have h1 := hc.choose_spec.2
    rw [QuotientGroup.eq] at h1
    exact QuotientGroup.eq.2 ((hJU _ hc.choose_spec.1 _ hx).1 h1)
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_reps (Umax D.host.E D.R.nV) Ds hfinU
  have hH : ∀ f : GAf D.host.E D.R.nV → (P.M.loc i).wt.W, (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ f = f) →
      NG.heckeD (P.M.loc i).J Ds f = ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ f := by
    intro f hf
    have hf' : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → NG.rt D.host.E D.R.nV κ f = f :=
      fun κ hκ ht => hf κ ⟨hκ, ht⟩
    have e1 : NG.heckeD (P.M.loc i).J Ds f = NG.heckeD (Umax D.host.E D.R.nV) Ds f := by
      funext g
      simp only [NG.heckeD]
      refine GlobalTheory.HeckeScalarAll.finsum_cosets_eq (P.M.loc i).J (Umax D.host.E D.R.nV) Ds (fun x => f (g * x)) hJU ?_
      intro x hx x' hx' hu
      have ht := GlobalTheory.HeckeScalarAll.trivOutside_mul (GlobalTheory.HeckeScalarAll.trivOutside_inv (hDs x hx)) (hDs x' hx')
      have h1 := congrFun (hf' _ hu ht) (g * x)
      simp only [NG.rt, LinearMap.coe_mk, AddHom.coe_mk] at h1
      rw [mul_assoc, mul_inv_cancel_left] at h1
      exact h1.symm
    rw [e1]
    exact GlobalTheory.HeckeScalarSph.heckeD_eq_sum (v := sp.v) hDs hR1 hR2 hf'
  obtain ⟨cX, hcX⟩ := GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) sp Ds hDs hbi R hR1 hR2
  obtain ⟨cX', hcX'⟩ := GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible D.host.E D.R.nV _ _ _ (P.H.av.irr i Q') sp Ds hDs hbi R hR1 hR2
  have hcI := GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) _ R cX hcX
  have hcI' := GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart D.host.E D.R.nV _ _ _ (P.H.av.irr i Q') _ R cX' hcX'
  have hc1 : c = cX := by
    have e1 := hc
    rw [hH F (hK F hFT), hcI F hF (hK F hFT)] at e1
    exact smul_left_injective ℂ hF0 e1.symm
  have hc2 : c' = cX' := by
    have e1 := hc'
    rw [hH F' (hK F' hF'T), hcI' F' hF' (hK F' hF'T)] at e1
    exact smul_left_injective ℂ hF'0 e1.symm
  rw [hc1, hc2]
  let π : NG.AutRep D.host.E D.R.nV := ⟨(P.M.loc i).wt, P.H.av.S i Q, P.H.av.irr i Q⟩
  let π' : NG.AutRep D.host.E D.R.nV := ⟨(P.M.loc i).wt, P.H.av.S i Q', P.H.av.irr i Q'⟩
  obtain ⟨σ, hσ⟩ := GlobalTheory.LocCompSplit.exists_isLocS π sp
  obtain ⟨σ', hσ'⟩ := GlobalTheory.LocCompSplit.exists_isLocS π' sp
  have hcl := hcls σ σ' hσ hσ'
  obtain ⟨E⟩ : Nonempty (σ.ρ.Equiv σ'.ρ) := by
    have h2 : σ.cl = σ'.cl := eq_of_heq (Sigma.mk.inj hcl).2
    exact GlobalTheory.SmGL.IrrRep.cl_eq_iff.1 h2
  have hσ0 := hσ
  obtain ⟨ι, T0, hι, hιc, hT0i, hT0S, hT0e⟩ := hσ
  obtain ⟨ι', T0', hι', hιc', hT0i', hT0S', hT0e'⟩ := hσ'
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique _ sp ι ι' hι hι' hιc hιc'
  obtain ⟨a, ha0, hafix⟩ := GlobalTheory.T.splitLocalComponent_has_fixedVector_of_isotypic D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) sp σ hσ0 ι hι hιc F hF hF0 (hK F hFT)
  have hT0H : ∀ v, T0 (∑ γ ∈ R, σ.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) v) =
      ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ (T0 v) := by
    intro v

    rw [map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hT0e γ (hDs γ (hR1 γ hγ)) v
  have hT0H' : ∀ v, T0' (∑ γ ∈ R, σ'.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) v) =
      ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ (T0' v) := by
    intro v

    rw [map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hT0e' γ (hDs γ (hR1 γ hγ)) v
  have hT0fix : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ (T0 a) = T0 a := by
    intro κ hκ
    rw [← hT0e κ hκ.2 a, hafix κ hκ]
  have hHa : ∑ γ ∈ R, σ.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) a = cX • a := by
    apply hT0i
    rw [hT0H, map_smul]
    exact hcX (T0 a) (hT0S a) hT0fix
  have hE : ∀ g v, E.toLinearEquiv (σ.ρ g v) = σ'.ρ g (E.toLinearEquiv v) := fun g v =>
    LinearMap.congr_fun (E.isIntertwining' g) v
  have ha'0 : E.toLinearEquiv a ≠ 0 := fun h => ha0 (E.toLinearEquiv.injective (by rw [h, map_zero]))
  have hHa' : ∑ γ ∈ R, σ'.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) (E.toLinearEquiv a) =
      cX • E.toLinearEquiv a := by

    simp only [← hE, ← map_sum, hHa, map_smul]
  have hT0fix' : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v,
      NG.rt D.host.E D.R.nV κ (T0' (E.toLinearEquiv a)) = T0' (E.toLinearEquiv a) := by
    intro κ hκ
    rw [← hT0e' κ hκ.2, ← hE, hafix κ hκ]
  have key := hcX' (T0' (E.toLinearEquiv a)) (hT0S' _) hT0fix'
  rw [← hT0H', hHa', map_smul] at key
  have hne : T0' (E.toLinearEquiv a) ≠ 0 := fun h => ha'0 (hT0i' (by rw [h, map_zero]))
  exact smul_left_injective ℂ hne key
end GlobalTheory.LocEigAgree
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.CoefDuty

theorem sameLoc_iff_heckeCong_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w → ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'), (i = i' ↔ ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) - iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') ∈ (A.pl.plB w).nonunits) := by
  intro D cf jE A M C tup big L hB j w i i' hi hi' x x'
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB
  have hiC : ∀ (a : L.X.nd.Loc) (ha : a ∈ L.X.nd.locs j w) (z : L.X.nd.O a),
      iotaO L.X.nd L.Y.naut a z = Sp.iotaC j w (Sp.phO j w a ha z) := by
    intro a ha z
    rw [← Sp.iotaC_coh j w a ha z]
    show ((L.Y.naut.iotaQC a).toRingHom.comp (L.Y.naut.iotaQ a)) (algebraMap _ _ z) = _
    rw [RingHom.comp_apply, Au.iotaQ, Au.iotaQC]
    rfl
  have key : ∀ (a : L.X.nd.Loc) (ha : a ∈ L.X.nd.locs j w) (y : L.X.nd.O a),
      iotaO L.X.nd L.Y.naut a y ∈ (A.pl.plB w).nonunits ↔ y ∈ IsLocalRing.maximalIdeal (L.X.nd.O a) := by
    intro a ha y
    have hw : L.X.nd.w a = w := ((L.X.nd.locs_mem j w a).1 ha).2
    subst hw
    obtain ⟨h, e⟩ := Au.kFbar a y
    rw [ValuationSubring.mem_nonunits_iff]
    have e1 : (A.pl.plB (L.X.nd.w a)).valuation (iotaO L.X.nd L.Y.naut a y) =
        (A.pl.plB (L.X.nd.w a)).valuation ((⟨_, h⟩ : A.pl.plB (L.X.nd.w a)) : ℂ) := rfl
    rw [e1, ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff,
      ← IsLocalRing.residue_eq_zero_iff, ← map_eq_zero (L.Y.naut.kFbar a), ← e]
    simp only [EmbeddingLike.map_eq_zero_iff]
  have gen : ∀ v k, GenAt D (D.what₂.places.resChar w) (C.Q w) v k ↔
      GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by
    intro v k; rw [Sp.Qc_eq]
  constructor
  · rintro rfl v k hvk
    have hvk' := (gen v k).1 hvk
    have e1 := Sp.ptX_hT j w i hi x v k hvk'
    have e2 := Sp.ptX_hT j w i hi' x' v k hvk'
    have hc : Formalism.L2.NCov.cls (Sp.ptX j w i hi x).1 = Formalism.L2.NCov.cls (Sp.ptX j w i hi' x').1 :=
      (Sp.ptX j w i hi x).2.1.trans (Sp.ptX j w i hi' x').2.1.symm
    generalize (Sp.ptX j w i hi x).1 = ψ at e1 hc
    generalize (Sp.ptX j w i hi' x').1 = ψ' at e2 hc
    generalize (⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk', rfl⟩⟩ : heckeAlg Sp.B j w) = t at e1 e2
    have hmem : t - algebraMap _ _ (ψ t) ∈ Formalism.L2.NCov.cls ψ' := by
      rw [← hc, Formalism.L2.NCov.cls, RingHom.mem_ker]
      change IsLocalRing.residue _ (ψ (t - algebraMap _ _ (ψ t))) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self, map_zero]
    rw [Formalism.L2.NCov.cls, RingHom.mem_ker] at hmem
    change IsLocalRing.residue _ (ψ' (t - algebraMap _ _ (ψ t))) = 0 at hmem
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, map_sub, sub_eq_zero, ← e1, ← e2] at hmem
    have r := GlobalTheory.PtLocalEig.residue_map_equiv (Sp.phO j w i hi).symm hmem
    simp only [RingEquiv.symm_apply_apply] at r
    rw [← map_sub]
    refine (key i hi _).2 ?_
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, r, sub_self]
  · intro H
    apply Sp.mx_inj j w hi hi'
    rw [← (Sp.ptX j w i hi x).2.1, ← (Sp.ptX j w i' hi' x').2.1]
    refine GlobalTheory.PtLocalEig.cls_eq_of_residue _ _ _ ?_
    rintro _ ⟨v, k, hvk, rfl⟩
    rw [← Sp.ptX_hT j w i hi x v k hvk, ← Sp.ptX_hT j w i' hi' x' v k hvk]
    have h1 := H v k ((gen v k).2 hvk)
    have hz : iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') =
        iotaO L.X.nd L.Y.naut i ((Sp.phO j w i hi).symm
          (Sp.phO j w i' hi' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x'))) := by
      rw [hiC i hi, hiC i' hi', RingEquiv.apply_symm_apply]
    rw [hz, ← map_sub, key i hi, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at h1
    have h2 := GlobalTheory.PtLocalEig.residue_map_equiv (Sp.phO j w i hi) h1
    rwa [RingEquiv.apply_symm_apply] at h2
end GlobalTheory.CoefDuty
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.L2.Host
namespace GlobalTheory.LocCompTy
open GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

theorem blockEig_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (PI : D.naut.AV i)
    (k : Fin 2) (v : D.nd.PlG k) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (s : SplitPlace D.host.E)
    (hsw : s.w = D.naut.plGw k v) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E)
    (hcont : Continuous c) (hci : ∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x)
    (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (x : GAf D.host.E D.R.nV) (hx : TrivOutside {s.v} x)
    (hh : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈
      GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t) :
    NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w)
      (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  obtain ⟨ψ₀, ξ, hψ, hξ, hlev⟩ := P.H.level.uni i j hj k v s hsw
  have hcv := GlobalTheory.SplitConjVal.valuation_eq s c hcont hci
  obtain ⟨h1, h2⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x) hh
  obtain ⟨i1, -⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x)⁻¹
    (by
      have := (GlobalTheory.BlockType.blockGrp _ _ _).inv_mem hh
      convert this using 1
      exact map_inv (Matrix.GeneralLinearGroup.map (n := Fin (D.R.r + D.R.t)) c.toRingHom) _)
  have huni : NG.UniRT s D.R.r (s.loc D.R.nV x) := by
    refine ⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩,
      fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h1 a b)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (i1 a b)
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at ha; omega
      · rwa [sub_zero] at this
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at hlt; omega
      · rwa [sub_zero] at this
    · subst he
      have := h2 a a ha
      split_ifs at this with e
      · exact this
      · exact absurd rfl e
  have hxJ : x ∈ (P.M.loc i).J := (hlev.mem x hx).2 huni
  have hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hrt := hTS.2 ⟨x, hxJ⟩
  let h : GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E) :=
    Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)
  have hh' : h ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := hh
  have hdet := GlobalTheory.BlockConjDet.val_det_mul_sub_one_lt hh'
  have hne2 : (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub, Valuation.map_neg, map_one] at hdet
    exact lt_irrefl _ hdet
  have hc_det : c (NG.detDD s D.R.r (s.loc D.R.nV x)) =
      (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {y : Fin D.R.nV // D.R.r ≤ y.val} :=
      { toFun := fun a => ⟨Fin.natAdd D.R.r a, by simp⟩
        invFun := fun y => ⟨y.1.val - D.R.r, by
          have h1 := y.1.2; have h2 := y.2; change y.1.val < D.R.r + D.R.t at h1; omega⟩
        left_inv := fun a => by ext; simp
        right_inv := fun y => by ext; simp; have := y.2; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e]
    rw [show c _ = c.toRingHom _ from rfl, RingHom.map_det]
    congr 1
  have hF0 : NG.detDD s D.R.r (s.loc D.R.nV x) ≠ 0 := fun h0 => hne2 (by rw [← hc_det, h0, map_zero])
  let u := Units.mk0 _ hF0
  have hchr := hlev.chr x hxJ hx u rfl
  have hsup : ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV x)) = 1 := hψ.1 _ (by
    unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · have := h2 p q h.2
      split_ifs at this with e
      · rw [e] at h; omega
      · rwa [sub_zero] at this
    · rw [map_zero]; exact zero_lt_one)
  have hμ : GlobalTheory.NPin.IsComp (P.tp.tup (D.nd.mu i) j) s.w ((P.tp.tup (D.nd.mu i) j).loc s.w) :=
    ⟨GlobalTheory.HeckeComp.smooth_loc _ _, fun _ => rfl⟩
  have hξμ := GlobalTheory.ConjDense.eq_of_agree s c hcont hci ((P.tp.tup (D.nd.mu i) j).loc s.w) ξ hμ.1 hξ.1
    (fun k => by rw [hξ.2 k, hμ.2 k]) u
  have hbc : GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w) h =
      ((((P.tp.tup (D.nd.mu i) j).loc s.w) (Units.map c.toMonoidHom u) : ℂˣ) : ℂ) :=
    GlobalTheory.BlockType.blockChar_eq _ _ _ (by rw [← hc_det]; rfl)
  change _ = GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w) h • _
  rw [hbc, ← hξμ, hrt, hchr, hsup, one_mul]
end GlobalTheory.LocCompTy
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
open Filter Topology
namespace GlobalTheory.TypeBlockFix
variable {F : Type} [Field F] [NumberField F] {F' : Type} [Field F'] [NumberField F']
section loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end loc
end GlobalTheory.TypeBlockFix
namespace GlobalTheory.TypeBlockFix
open ValuativeRel
end GlobalTheory.TypeBlockFix
namespace GlobalTheory.TypeBlockFix
open Filter Topology
end GlobalTheory.TypeBlockFix
open GlobalTheory.TypeBlockFix in
theorem GlobalTheory.typeVec_blockChar_fixedPlace_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  intro hL D P S hS i k v s hw hsw _hT c hc hci Q
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp; omega⟩
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i Q)
  rw [P.H.av.typeV] at hy
  have hfT : (P.M.loc i).real y ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
  refine ⟨(P.M.loc i).real y, hy, fun h0 => hy0 ((P.M.loc i).real_inj (h0.trans (map_zero _).symm)), ?_⟩
  obtain ⟨ψ₀, ξ, hψ, hξ, hLv⟩ := P.H.level.uni i j hj k v s hsw
  intro x hx hblk
  set G := s.loc D.R.nV x with hG
  set h := Matrix.GeneralLinearGroup.map c.toRingHom G with hh
  have hent : ∀ a b, h.val a b = c (G.val a b) := fun a b => rfl
  have hient : ∀ a b, (h⁻¹).val a b = c ((G⁻¹).val a b) := by
    intro a b; rw [hh, ← map_inv]; rfl
  have hle : ∀ y, ValuativeRel.valuation _ (c y) ≤ 1 → Valued.v y ≤ 1 := fun y hy' =>
    (v_map_le_one_iff _ _ c hc y).1 ((complRel_le_one _ _).1 hy')
  have hlt : ∀ y, ValuativeRel.valuation _ (c y) < 1 → Valued.v y < 1 := fun y hy' =>
    (v_map_lt_one_iff _ _ c hc y).1 ((complRel_lt_one _ _).1 hy')
  have hI : ∀ a b, Valued.v (G.val a b) ≤ 1 := fun a b =>
    hle _ (by rw [← hent]; exact GlobalTheory.BlockType.val_le_one_of_mem_KO hblk.1 a b)
  have hI' : ∀ a b, Valued.v ((G⁻¹).val a b) ≤ 1 := fun a b =>
    hle _ (by rw [← hient]; exact GlobalTheory.BlockType.val_le_one_of_mem_KO ((KO _ _).inv_mem hblk.1) a b)
  have hcol : ∀ a (b : Fin D.R.nV), b.val < D.R.r → a ≠ b → Valued.v (G.val a b) < 1 := by
    intro a b hb hab
    refine hlt _ ?_
    have := hblk.2 a ⟨b.val, hb⟩
    rw [← hent]
    have e : b = Fin.castAdd D.R.t ⟨b.val, hb⟩ := Fin.ext rfl
    rw [← e] at this
    change ValuativeRel.valuation _ (h.val a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) _) a b) < 1 at this
    rw [Matrix.one_apply_ne hab, sub_zero] at this
    exact this
  have hdiag : ∀ (b : Fin D.R.nV), b.val < D.R.r → Valued.v (G.val b b - 1) < 1 := by
    intro b hb
    refine hlt _ ?_
    have := hblk.2 b ⟨b.val, hb⟩
    have e : b = Fin.castAdd D.R.t ⟨b.val, hb⟩ := Fin.ext rfl
    rw [← e] at this
    change ValuativeRel.valuation _ (h.val b b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) _) b b) < 1 at this
    rw [Matrix.one_apply_eq, hent] at this
    rwa [map_sub, map_one]
  have hpara : NG.ParaRT s D.R.r G := by
    refine ⟨mem_GLint_of_entries _ G (fun a b => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hI a b))
      (fun a b => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hI' a b)), ?_⟩
    · intro a b ha hb
      exact hcol a b hb (fun e => by rw [e] at ha; omega)
  have huni : NG.UniRT s D.R.r G := by
    refine ⟨hpara, fun a b ha hb => ⟨fun hab => hcol a b hb (fun e => by rw [e] at hab; omega), fun e => ?_⟩⟩
    subst e; exact hdiag a ha
  have hmem : x ∈ (P.M.loc i).J := (hLv.mem x hx).2 huni
  have hcdet : c (NG.detDD s D.R.r G) = (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {a : Fin D.R.nV // D.R.r ≤ a.val} :=
      { toFun := fun b => ⟨Fin.natAdd D.R.r b, by simp⟩
        invFun := fun a => ⟨a.1.val - D.R.r, by have h1 : a.1.val < D.R.r + D.R.t := a.1.2; omega⟩
        left_inv := fun b => by ext; simp
        right_inv := fun a => by ext; simp; have := a.2; omega }
    rw [NG.detDD, show c (Matrix.of fun a b : {x : Fin D.R.nV // D.R.r ≤ x.val} => G.val a.1 b.1).det =
      c.toRingHom (Matrix.of fun a b : {x : Fin D.R.nV // D.R.r ≤ x.val} => G.val a.1 b.1).det from rfl,
      RingHom.map_det, ← Matrix.det_submatrix_equiv_self e]
    congr 1
  have hdet : NG.detDD s D.R.r G ≠ 0 := by
    intro h0
    exact (det_ne_zero_of_mem_blockGrp _ _ _ _ hblk) (hcdet.symm.trans (by rw [h0, map_zero]))
  refine (hfT.2 ⟨x, hmem⟩).trans ?_
  congr 1
  rw [hLv.chr x hmem hx (Units.mk0 _ hdet) rfl]
  have hsd : Valued.v (NG.supDiag s D.R.r G) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    split_ifs with hab
    · exact hcol a b hab.2 (fun e => by rw [e] at hab; omega)
    · simp
  rw [hψ.1 _ hsd, one_mul, comp_agree _ s _ ξ _ c hc hci hξ (hS.mu i s.w hw j hj)]
  exact (GlobalTheory.BlockType.blockChar_eq _ _ _ hcdet).symm
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PartOrthPin
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i)) → GlobalTheory.ThetaExh.PartOrth D.nd i := by
  intro hL D P i ⟨X⟩ σ σ' hne
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  have hni : ¬ (P.rep σ).Iso (P.rep σ') := fun h => hne (P.rep_inj σ σ' h)
  rw [X.φ_inner]
  exact GlobalTheory.IsotOrth.isotIn_orthogonal D D.R.r X.A X.ρ X.C X.B X.lin X.herm X.pos X.stab X.inv X.adm
    (P.rep σ) (P.rep σ') hni _ ((X.isot σ u).1 hu) _ ((X.isot σ' v).1 hv)
end GlobalTheory.PartOrthPin
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu := by
  intro hL D P S hS i k v hw
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hc := hS.mu i _ hw j hjj
  have hc' : IsComp (P.tp.tup (D.nd.mu i) j) (D.naut.plGw k v) ((P.tp.tup (D.nd.mu i) j).loc (D.naut.plGw k v)) :=
    ⟨GlobalTheory.HeckeComp.smooth_loc _ _, fun _ => rfl⟩
  rw [GlobalTheory.HeckeComp.eq_of_isComp hc' hc]
  exact GlobalTheory.MuTameQS.isTame_loc (GlobalTheory.MuTameQS.tameAt_mul ((P.cf.isMu0 j).tame _) (P.tp.xi_tame _ _))
end
end
