module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle123
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle453
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle450
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle247
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle242
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1676
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.GalAut
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle248
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle617
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeEquiv
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar

@[expose] public section

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutQuot
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
end GlobalTheory.AutQuot
namespace GlobalTheory.AutQuot
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
theorem locOf_eq_alt {π : NG.AutRep D.host.E D.R.nV} {w : PlE D.host} {x} (hx : LocAt π w x) :
    _root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep w = (T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x) := by
  have hex : ∃ x, LocAt (clsA π).rep w x := by
    obtain ⟨s, σ, hs, -, -⟩ := hx
    subst hs
    exact locAt_of_split _ s
  unfold _root_.GlobalTheory.AutQuot.locOf_alt
  rw [dite_eq_left hex, locAt_unique (rep_iso π) hex.choose_spec hx]
end
end GlobalTheory.AutQuot
namespace GlobalTheory.AutQuot
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
theorem f_sph_alt (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hv : NG.OverPl w v) : (∃ v', NG.OverPl w v' ∧ (clsA π).rep.SphericalAtPlace v') ↔ π.SphericalAtPlace v := by
  constructor
  · rintro ⟨v', hv', hs⟩
    rw [overPl_unique hv hv']
    exact _root_.UpperTheory.One.M.New.sphAt_iso (rep_iso π) hs
  · intro hs
    exact ⟨v, hv, _root_.UpperTheory.One.M.New.sphAt_iso (autIso_symm (rep_iso π)) hs⟩
theorem unr_locOf_of_sphAt (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (hs : π.SphericalAtPlace s.v) :
    D.naut.unr (_root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep s.w) := by
  obtain ⟨x, hx⟩ := locAt_of_split π s
  rw [_root_.GlobalTheory.AutQuot.locOf_eq_alt hL D T hx, T.unr, Equiv.apply_symm_apply]
  exact _root_.GlobalTheory.T.locRecT_unr_of_sphAt hL D π s x hx hs
theorem f_locPol_alt (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (w : PlE D.host)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hc : IsConjPl D.host w s.w) (hu : IsUnif D.host.E s.v ϖ)
    (J : Subgroup (GAf D.host.E D.R.nV)) (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV))
    (f : GAf D.host.E D.R.nV → π.W) (hf : f ∈ π.S) (hf0 : f ≠ 0)
    (hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) (c : ℕ → ℂ)
    (hc' : ∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) :
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      galPol D.naut (D.naut.lpTw (_root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep w) ((1 - (D.R.nV : ℝ)) / 2)) := by
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_localComponent_conj_splitPlace D π s w hc
  obtain ⟨hun, hpol⟩ := _root_.GlobalTheory.T.spherical_vector_fixed_local_alt hL D π s w ϖ hc hu J hJ f hf hf0 hfix c hc' x hx
  rw [_root_.GlobalTheory.AutQuot.locOf_eq_alt hL D T hx]
  have hu2 : D.naut.unr (D.naut.lpTw ((T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x))
      ((1 - (D.R.nV : ℝ)) / 2)) := by
    rw [T.unr, T.tw, Equiv.apply_symm_apply]; exact hun
  unfold galPol
  rw [T.frobEig _ _ hu2, T.tw, Equiv.apply_symm_apply]
  exact hpol
theorem e_locOf_eq_locRecT_of_isLocS (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E))) (hσ : IsLocS π.S s σ) :
    T.e s.w (_root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep s.w) =
      _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls σ) := by
  rw [_root_.GlobalTheory.AutQuot.locOf_eq_alt hL D T ⟨s, σ, rfl, hσ, HEq.rfl⟩, Equiv.apply_symm_apply]

theorem exists_nbc_auSide_true_of_empty (hE : IsEmpty D.nd.Loc) :
    ∃ (C : NBC D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt (setBC D C)), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (setBC D C) T A :=
  ⟨{ _root_.GlobalTheory.AutQuot.boundaryConditionOfNoLocal hL D T hE with
      sphAU := fun _ X w => ∃ v, NG.OverPl w v ∧ (AUq.rep X).SphericalAtPlace v
      embAV_sph := fun i => isEmptyElim i },
    { cls := fun _ _ _ π => clsA π
      surj := fun _ _ _ X => ⟨X.rep, AUq.cls_rep X⟩
      iso := fun _ _ _ π π' => clsA_eq_iff π π'
      mult := fun _ _ _ π => GlobalTheory.T.automorphic_multiplicity_eq_of_iso _ _ _ _ (rep_iso π)
      sph := fun _ _ _ π w v _ hv => _root_.GlobalTheory.AutQuot.f_sph_alt D π w v hv
      sat := fun _ _ _ π v w hv Dv hα => f_sat D π v w hv Dv hα
      clsWt := fun _ _ _ a => clsW a
      surjWt := fun _ _ _ Y => ⟨Y.rep, WtQ.cls_rep Y⟩
      isoWt := fun _ _ _ a b => clsW_eq_iff a b
      wt := fun _ _ _ π a hd => f_wt D π a hd
      infW := fun _ _ _ a τ lam hl => f_infW D a τ lam hl
      locUnr := fun _ _ _ π s hs => _root_.GlobalTheory.AutQuot.unr_locOf_of_sphAt hL D T π s hs
      locPol := fun _ _ _ π s w ϖ hc hu J hJ f hf hf0 hfix c hc' => _root_.GlobalTheory.AutQuot.f_locPol_alt hL D T π s w ϖ hc hu J hJ f hf hf0 hfix c hc' },
    fun _ _ _ π s σ hσ => _root_.GlobalTheory.AutQuot.e_locOf_eq_locRecT_of_isLocS hL D T π s σ hσ⟩
end
end GlobalTheory.AutQuot
open Formalism.BasicNotions GlobalTheory.HeightCounting in
theorem GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), IsEmpty D.nd.Loc →
    ∀ T : GlobalTheory.RowTie.WDTie D.nd D.naut, ∃ (C : NBC D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt (setBC D C)), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (setBC D C) T A :=
  fun hL D hE T => _root_.GlobalTheory.AutQuot.exists_nbc_auSide_true_of_empty hL D T hE
end
end
end

section



section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalN
theorem galoisRep_definiteUnitary_alt : _root_.GlobalTheory.GalAut.galoisRep_definiteUnitary_tyz := by
  intro H1 H3 _ H6 H7 H8 H9 H10 E Ω _ _ _ _ _ _ hE n hn π hπ lam hlam l _ ι hunr
  obtain ⟨c, a, d, h, P, ρ, m, σ, hP, hloc, hsplit⟩ := _root_.UpperTheory.BaseChangeIdentities.base_change_speh_narrow_swap H1 E hE n hn π hπ
  let J : (Σ i : Fin c, Fin (d i)) → (E →+* Qbar l) → Multiset ℤ := fun x τ =>
    (m x.1 (ι.toRingHom.comp τ)).map (fun z => ⌊(GlobalTheory.GalAut.shiftF n (d x.1) x.2 - z).re⌋)
  have hJ : ∀ x τ, (J x τ).map (fun k : ℤ => (k : ℂ)) =
      (m x.1 (ι.toRingHom.comp τ)).map (fun z => GlobalTheory.GalAut.shiftF n (d x.1) x.2 - z) := by
    intro x τ
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun z hz => ?_
    obtain ⟨j, hj⟩ := GlobalTheory.GalAut.int_shift hP (hlam _) x.1 x.2 hz
    exact GlobalTheory.GalAut.cast_floor_re hj
  have hnd : ∀ i τ, (m i τ).Nodup := fun i τ => GlobalTheory.GalAut.nodup_of_parts hP (hlam τ) i
  have hsph : ∀ i (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal →
      ∀ σ' : SmIrr (GL (Fin (a i)) (w.adicCompletion E)), (P i).IsLocComp w σ' →
        GlobalTheory.LGrp.IsSpherical σ'.ρ (GlobalTheory.LFun.KGL w (n := (a i))) := fun i w hw σ' h' =>
    GlobalTheory.SphBC.isSpherical_of_isUnramU E hE n π hπ c a d h P ρ m σ hP hloc hsplit w (hunr w hw) i σ' h'
  have hpc := fun x : (Σ i : Fin c, Fin (d i)) => _root_.GlobalTheory.CsdTwistGal.exists_galRep_csd_twist_alt_alt H3 H6 H7 H8 H9 H10 E Ω hE l ι (a x.1) (hP.pos x.1).1 (P x.1)
    (hP.csd x.1) (m x.1) (hP.inf x.1) (hnd x.1) (GlobalTheory.GalAut.shiftF n (d x.1) x.2) (J x) (hJ x)
  choose r hrc hrcrys hrfrob using hpc
  have hsize : ∑ x : (Σ i : Fin c, Fin (d i)), a x.1 = n := by
    rw [Fintype.sum_sigma, ← h]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  obtain ⟨R, hRc, hRcrys, hRch⟩ := GlobalTheory.BlockSum.main H9 E Ω l (Σ i : Fin c, Fin (d i)) (fun x => a x.1) n hsize r hrc
  have hS : ∀ w, IsSplitAt w → ∀ (σw : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σw.ρ → GlobalTheory.LFun.HasSatGL w σw.ρ T →
      ∃ S : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ (S i)) ∧
        ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
          T.map (fun z => (z : ℂ)) := fun w hs σw T hc ht =>
    GlobalTheory.SatInd.satake_locProd_speh E w c n a d h (ρ · w) (σ · w) (fun i => (hP.pos i).2) (fun i => (hloc i w).2.2) T
      (GlobalTheory.SplitSatake.hasSatGL_of_isCompAlong_split E n π hπ w hs _ _ σw.ρ (locProd h w (σ · w)) hc (hsplit w hs) T ht)
  have hq : ∀ w : HeightOneSpectrum (𝓞 E), (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := fun w h0 =>
    w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hprod : ∀ w, IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (σw : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σw.ρ → GlobalTheory.LFun.HasSatGL w σw.ρ T →
      ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
      ∏ x, (r x (g ^ (-1 : ℤ))).val.charpoly = (T.map fun z : ℂˣ =>
          Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod := by
    intro w hs hl σw T hc ht B g hB hg
    obtain ⟨S, hS1, hS2⟩ := hS w hs σw T hc ht
    rw [GlobalTheory.satake_linear_factors_regroup (Qbar l) ι c d S T _ (hq w) (((n : ℂ) - 1) / 2) hS2, Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ =>
      hrfrob ⟨i, k⟩ w hs hl (ρ i w) (hP.loc i w) (S i) (hS1 i) B g hB hg
  have hsg : ((-1 : ℤˣ) : ℤ) = -1 := rfl
  refine ⟨⟨R, ?_, ?_⟩, ?_⟩
  · have hj : (fun τ => ∑ x, J x τ) = GlobalTheory.GalDef.jumpsOf ι lam := by
      funext τ
      apply Multiset.map_injective (f := fun k : ℤ => (k : ℂ)) Int.cast_injective
      rw [GlobalTheory.GalAut.map_cast_sum]
      simp only [hJ]
      rw [Fintype.sum_sigma]
      have e1 : ∀ i : Fin c, ∑ k : Fin (d i), (m i (ι.toRingHom.comp τ)).map (fun z => GlobalTheory.GalAut.shiftF n (d i) k - z) =
          (spehInf (d i) (m i (ι.toRingHom.comp τ))).map (fun z => ((n : ℂ) - 1) / 2 - z) := fun i =>
        GlobalTheory.DefiniteBC.spehInf_map_sub_eq_sum_twists (d i) (m i (ι.toRingHom.comp τ)) (((n : ℂ) - 1) / 2)
      rw [Finset.sum_congr rfl fun i _ => e1 i, ← GlobalTheory.GalAut.map_sub_sum, hP.weight _ _ (hlam _)]
      unfold GlobalTheory.GalDef.jumpsOf infOfWeight
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun k _ => ?_
      simp only [Function.comp_apply]
      push_cast; ring
    rw [← hj]
    exact hRcrys J fun x => hrcrys x fun w hw => ⟨ρ x.1 w, hP.loc x.1 w, hsph x.1 w hw _ (hP.loc x.1 w)⟩
  · intro w hs hl hU σw T hc ht B g hB hg
    rw [hsg]
    show (R (g ^ (-1 : ℤ))).val.charpoly = _
    rw [hRch]
    exact hprod w hs hl σw T hc ht B g hB hg
  · intro t ht hrun hstr
    obtain ⟨w, hs, hl, hU, σw, T, ν, hc, ht', hν, hle⟩ := hstr
    obtain ⟨S, hS1, hS2⟩ := hS w hs σw T hc ht'
    have htemp : ∀ i, ∀ s ∈ S i, ‖(s : ℂ)‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) := fun i s hs =>
      (satake_window E (a i) (P i) (hP.csd i) w (ρ i w) (hP.loc i w) (S i) (hS1 i) s hs).2
    have ht1 : 1 ≤ t := by omega
    obtain ⟨i0, hi0⟩ := string_forces_long_part E w c d S T t ν ht1 htemp hν hS2 (by rw [GlobalTheory.GalAut.lift_eq]; exact hle)
    have hne : ∀ i τ, m i τ ≠ 0 := fun i τ h0 => by
      have h1 := (hP.inf i τ).1
      rw [h0, Multiset.card_zero] at h1
      have := (hP.pos i).1
      omega
    have hrunP : ∀ τ' p, GlobalTheory.GalDef.IsRunAt (lam τ') p t → d i0 = t ∧
        m i0 τ' = {(GlobalTheory.GalDef.wAt (lam τ') p : ℂ) + ((n : ℂ) - 1) / 2 - (p : ℕ) - ((t : ℂ) - 1) / 2} ∧
          ∀ j, j ≠ i0 → d j < t :=
      fun τ' p hp => GlobalTheory.GalDef.spehPart_is_run n t (lam τ') p ht hp c d (fun i => m i τ') (fun i => (hP.pos i).2)
        (fun i => hne i τ') (hP.weight τ' _ (hlam τ')) i0 hi0
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨p0, hp0⟩ := hrun τ0
    obtain ⟨hd0, hm0, -⟩ := hrunP τ0 p0 hp0
    have ha0 : a i0 = 1 := by
      have h1 := (hP.inf i0 τ0).1
      rw [hm0] at h1
      simpa using h1.symm
    let pp : (E →+* Qbar l) → ℕ := fun τ => (hrun (ι.toRingHom.comp τ)).choose
    have hpp : ∀ τ, GlobalTheory.GalDef.IsRunAt (lam (ι.toRingHom.comp τ)) (pp τ) t := fun τ => (hrun _).choose_spec
    let bot : (E →+* Qbar l) → ℤ := fun τ => (pp τ : ℤ) - GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) (pp τ)
    obtain ⟨ρR, hρc, -, hρch⟩ := GlobalTheory.BlockSum.main H9 E Ω l (Σ i : {i : Fin c // i ≠ i0}, Fin (d i)) (fun x => a x.1.1) _ rfl
      (fun x => r ⟨x.1.1, x.2⟩) (fun x => hrc _)
    let kk : Fin t → Σ i : Fin c, Fin (d i) := fun s => ⟨i0, Fin.cast hd0.symm (Fin.rev s)⟩
    refine ⟨_, ρR, fun s => Matrix.GeneralLinearGroup.det.comp (r (kk s)), bot, ?_, hρc, ?_, ?_, ?_⟩
    · rw [← hsize, Fintype.sum_sigma (fun x : Σ i : Fin c, Fin (d i) => a x.1), Fintype.sum_eq_add_sum_subtype_ne _ i0,
        Fintype.sum_sigma (fun x : Σ i : {i : Fin c // i ≠ i0}, Fin (d i) => a x.1.1)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hd0, ha0, mul_one]
      ring
    · intro s
      have hJk : ∀ τ, J (kk s) τ = {bot τ + ((s : ℕ) : ℤ)} := by
        intro τ
        show (m i0 (ι.toRingHom.comp τ)).map _ = _
        rw [(hrunP _ _ (hpp τ)).2.1, Multiset.map_singleton, Multiset.singleton_inj]
        have hs1 : (s : ℕ) + 1 ≤ t := s.isLt
        have e : GlobalTheory.GalAut.shiftF n (d i0) (kk s).2 - ((GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) (pp τ) : ℂ) +
            ((n : ℂ) - 1) / 2 - (pp τ : ℕ) - ((t : ℂ) - 1) / 2) = ((bot τ + ((s : ℕ) : ℤ) : ℤ) : ℂ) := by
          simp only [GlobalTheory.GalAut.shiftF, kk, bot, Fin.coe_cast, Fin.val_rev, hd0]
          rw [Nat.cast_sub hs1]
          push_cast
          ring
        rw [e]
        simp
      rw [show (fun τ => ({bot τ + ((s : ℕ) : ℤ)} : Multiset ℤ)) = J (kk s) from funext fun τ => (hJk τ).symm]
      exact GlobalTheory.GalAut.crystallineHodgeTate_det_rankOne ha0 (r (kk s)) (J (kk s)) (hrcrys (kk s) fun w hw => ⟨ρ i0 w, hP.loc i0 w, hsph i0 w hw _ (hP.loc i0 w)⟩)
    · intro τ p hp
      have e1 := (hrunP _ _ (hpp τ)).2.1
      have e2 := (hrunP _ _ hp).2.1
      rw [e1, Multiset.singleton_inj] at e2
      have e3 : (((pp τ : ℤ) - GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) (pp τ) : ℤ) : ℂ) =
          (((p : ℤ) - GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) p : ℤ) : ℂ) := by
        push_cast
        linear_combination -e2
      exact_mod_cast e3
    · intro w' hs' hl' hU' σ' T' hc' ht'' B g hB hg
      rw [hsg]
      show (ρR (g ^ (-1 : ℤ))).val.charpoly * ∏ s, (Polynomial.X - Polynomial.C
        (((Matrix.GeneralLinearGroup.det.comp (r (kk s))) (g ^ (-1 : ℤ)) : (Qbar l)ˣ) : Qbar l)) = _
      have e3 : ∏ x, (r x (g ^ (-1 : ℤ))).val.charpoly =
          (∏ k : Fin (d i0), (r ⟨i0, k⟩ (g ^ (-1 : ℤ))).val.charpoly) *
            ∏ x : (Σ i : {i : Fin c // i ≠ i0}, Fin (d i)), (r ⟨x.1.1, x.2⟩ (g ^ (-1 : ℤ))).val.charpoly := by
        rw [Fintype.prod_sigma, Fintype.prod_eq_mul_prod_subtype_ne _ i0, Fintype.prod_sigma]
      have e4 : ∏ s : Fin t, (Polynomial.X - Polynomial.C
          (((Matrix.GeneralLinearGroup.det.comp (r (kk s))) (g ^ (-1 : ℤ)) : (Qbar l)ˣ) : Qbar l)) =
          ∏ k : Fin (d i0), (r ⟨i0, k⟩ (g ^ (-1 : ℤ))).val.charpoly :=
        Fintype.prod_equiv (Fin.revPerm.trans (finCongr hd0.symm)) _ _ fun s =>
          (GlobalTheory.GalAut.charpoly_eq_of_one ha0 _).symm
      rw [← hprod w' hs' hl' σ' T' hc' ht'' B g hB hg, e3, hρch, e4, mul_comm]
end UpperTheory.GalN
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem eigenExponent_isIntegral_all_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ (j : Fin (Dof x).R.m) (g : ↥((Dof x).R.Psi)), ∃ z : ℤ, eExp (Dof x) j g = (z : ℚ) := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x j g => ?_
  exact ((Dof x).hc ((Dof x).eTau.symm g)).e_int j
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.eExp_integral_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ (j : Fin (Dof x).R.m) (g : ↥((Dof x).R.Psi)), ∃ z : ℤ, eExp (Dof x) j g = (z : ℚ) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.eigenExponent_isIntegral_all_stages_alt | exact _root_.GlobalTheory.HeightCounting.Up.eigenExponent_isIntegral_all_stages_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.eigenExponent_isIntegral_all_stages_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem fixedField_isStable_under_star_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ y : (Dof x).LL0, star (y : (Dof x).what₂.LL) ∈ (Dof x).LL0 := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x y => ?_
  exact (IntermediateField.normal_iff_forall_map_le.1 B.coeffGaloisSubfield_isGalois.to_normal
    (starRingEnd (Dof x).what₂.LL).toRatAlgHom) ⟨_, y.2, rfl⟩
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.star_mem_LL0 : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ y : (Dof x).LL0, star (y : (Dof x).what₂.LL) ∈ (Dof x).LL0 := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.fixedField_isStable_under_star_alt | exact _root_.GlobalTheory.HeightCounting.Up.fixedField_isStable_under_star_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.fixedField_isStable_under_star_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem globalNorm_all_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ i, ((Dof x).host.g i).Prime ∧ ∃ π : 𝓞 (Dof x).host.E, (π : (Dof x).host.E) ∈ (Dof x).host.K ∧ (π : (Dof x).host.E) * (Dof x).host.conj (π : (Dof x).host.E) = ((Dof x).host.g i : (Dof x).host.E) ∧ (π - 1) ∈ Ideal.span {(((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d : ℕ) : 𝓞 (Dof x).host.E)} := by
  intro _
  have aux : ∀ (K : Ctx) (Q : Pre), K.Over Q → ∀ i, (Q.host.g i).Prime ∧ ∃ π : 𝓞 Q.host.E, (π : Q.host.E) ∈ Q.host.K ∧
      (π : Q.host.E) * Q.host.conj (π : Q.host.E) = (Q.host.g i : Q.host.E) ∧
      (π - 1) ∈ Ideal.span {((Q.host.QS * Q.host.q * Q.host.d : ℕ) : 𝓞 Q.host.E)} := by
    rintro K Q ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ i
    exact ⟨K.P.H.g_prime i, K.ok.gnorm i⟩
  refine StepW.of_all fun K B f T w hO _ _ => ?_
  intro P x i
  exact aux K B.toPre hO i
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.exists_norm_element_congruent_one_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ i, ((Dof x).host.g i).Prime ∧ ∃ π : 𝓞 (Dof x).host.E, (π : (Dof x).host.E) ∈ (Dof x).host.K ∧ (π : (Dof x).host.E) * (Dof x).host.conj (π : (Dof x).host.E) = ((Dof x).host.g i : (Dof x).host.E) ∧ (π - 1) ∈ Ideal.span {(((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d : ℕ) : 𝓞 (Dof x).host.E)} := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.globalNorm_all_stages_alt | exact _root_.GlobalTheory.HeightCounting.Up.globalNorm_all_stages_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.globalNorm_all_stages_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem rows_mem_ringOfIntegers_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => Function.Injective (Dof x).what₂.OtoLL ∧
    ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y := by
  intro _
  refine Step.of_all fun K B f T _ _ _ _ w _ P x => ?_
  refine ⟨B.OtoLL_injective, B.Ks.toSubfield, fun y => ?_⟩
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨((show B.O from z) : B.Ks).2, B.O_int z⟩
  · rintro ⟨hy, hi⟩
    exact B.O_full y hy hi
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.integer_embedding_injective_range_integral_of_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => Function.Injective (Dof x).what₂.OtoLL ∧ ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.rows_mem_ringOfIntegers_alt | exact _root_.GlobalTheory.HeightCounting.Up.rows_mem_ringOfIntegers_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.rows_mem_ringOfIntegers_alt <;> assumption)
end
end
end

section



section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up.GridLg
theorem exists_large_grid_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x =>
    ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) ∧
      (GlobalTheory.BigTop.Fun.lamOf G).Ok ∧ (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x ∧ (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x) := by
  intro _ cDep
  have hd : AllSt fun K _ _ _ _ _ x => ∃ w0, GlobalTheory.LamTie.PlacesOk (Dof x).host (AbsolutelyIrreducibleSpan.q0 (Dof x)) w0 :=
    (Step.of_evLgG GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices).trans (Step.of_all fun K B f T _ hk _ H w _ P x => (H hk T w x.o.Z).2.2.2.2.2.2)
  refine (StepW.and (GlobalTheory.T.exists_grid_unit_gap_field_contains_values cDep) hd).trans (StepW.of_all fun K B f T w _ _ H P x => ?_)
  obtain ⟨G, hG⟩ := H.1 P x
  obtain ⟨w0, h0⟩ := H.2 P x
  exact ⟨G, hG, lamOf_ok _ _ _ _ G w0 h0, x.m.z.lev.C.trans rfl, rfl⟩
end GlobalTheory.HeightCounting.Up.GridLg
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.exists_lam_grid_fieldHas_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) ∧ (GlobalTheory.BigTop.Fun.lamOf G).Ok ∧ (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x ∧ (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.GridLg.exists_large_grid_alt | exact _root_.GlobalTheory.HeightCounting.Up.GridLg.exists_large_grid_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.GridLg.exists_large_grid_alt <;> assumption)
end
end
end

section



section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtId
variable {D : D7}
section Fam
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
variable {I0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Fam
section Asm
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Asm
section Cols
open GlobalTheory.Mem.Col2
variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px)
end Cols
section State
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
variable {P : Pre2 K w} (x : St P)
theorem exists_matrix_input_identity_frame_of_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ w P x =>
    ∃ m : InMt x.r.Y (cfOf x) w.I.xi (QOf P), ∀ i, GlobalTheory.MtRead.IdFrame x.r.Y.hF (m.ad.PV i) :=
  fun _ => by
    unfold AllSt
    exact StepW.of_all fun _ _ _ _ _ _ _ hs _ x => hs.1.elim fun pin => inMt_state x pin
end State
end GlobalTheory.MtId
end
end
end
end
