module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle776
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle762
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle713
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle009
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle088
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle087
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle086
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistedDualFrobeniusCompatibility
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.ExistsZalgOfCenterU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle008
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Gu

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem assemble (H : HypothesesH) (hFam : SumFam) (hHalf : Half) (hStr : Strings) (hUni : CompUnique) (hRec : RecTot)
    (hFrob : FrobTot) (hPol : PolOfFrob) (hLink : SatLink) (hConj : SatConj) (hIrr : IrrCase) : GalUnitary := by
  intro E Ω _ _ _ _ _ _ hE l _ _ ι n hn π hπ
  obtain ⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩ :=
    GlobalTheory.BcSpeh.bcSpeh_of_baseChange (GlobalTheory.BaseChangeBridge.main H.litN.aut.bc H.litN.loc.bern)
      (GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual H.litN.aut.mw) E hE n hn π hπ
  have hc : 1 ≤ c := by
    rcases c with _ | c
    · simp at hsum; omega
    · omega
  have hint : ∀ i (k : Fin (d i)) τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j := fun i k τ => by
    obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn π hπ τ
    exact (hStr n c d (m · τ) lam (hP.weight τ lam hl)).1 i k
  choose r₀ HT₀ h₀ hw₀ using fun i (k : Fin (d i)) =>
    hHalf E Ω l ι (a i) (hP.pos i).1 (P i) (hP.csd i) (ρ i) (hP.loc i) (m i) (hP.inf i) (ex n (d i) k) (hint i k)
  choose r₁ h₁ hi₁ using fun i => hFam E Ω l ι (d i) (hP.pos i).2 (fun _ => a i) (fun _ => (hP.pos i).1) (d i * a i) (by simp)
    (r₀ i) _ (HT₀ i) (h₀ i)
  obtain ⟨r, hr, hi⟩ := hFam E Ω l ι c hc (fun i => d i * a i) (fun i => Nat.mul_pos (hP.pos i).2 (hP.pos i).1) n hsum r₁ _ _ h₁
  have hpar : ∀ w, ParAt ι r w (totPar n d (ρ · w)) := hr.par
  have hF : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ S : Fin c → Multiset ℂˣ,
      (∀ i, (CG.mk (P i)).HasSat w (S i)) → FrobEig ι r w (algSat n (normV w) (satTot w d S)) := fun w hw S hS =>
    hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S (fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS i)) (hpar w)
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ S : Fin c → Multiset ℂˣ, ∀ i, (CG.mk (P i)).HasSat w (S i) := by
    filter_upwards [ev_notMem (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w h1 h2
    exact ⟨h1, Classical.skolem.1 h2⟩
  refine ⟨r, _, hr.cont, hr.ss, fun w hw hu A hA => ?_, hr.ht, fun τ lam hl => ?_, fun w hw τ hτ => ?_, ?_, fun hirr => ?_⟩
  · choose S hSat using fun i => (satLoc H.toClassicalTheorems E (a i) w (ρ i w)).1 (by
      obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1
        (GlobalTheory.SphBC.isSpherical_of_isUnramU E hE n π hπ c a d hsum P ρ m σ hP hS hsplit w hu i (ρ i w) (hP.loc i w))
      exact ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩)
    exact (hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S hSat (hpar w) A hA).1
  · rw [← (hStr n c d (m · (ι.toRingHom.comp τ)) lam (hP.weight _ lam hl)).2]
    simp only [← hw₀]

    simp only [← Multiset.coe_mapAddMonoidHom, map_sum]
  · exact (locGlob_iff ι r w τ).2 ((hpar w).congr (hRec E Ω n c a d hsum P w (ρ · w) (σ · w) hP.pos (hP.loc · w) (hS · w) τ
      (hUni E n π hπ w hw _ _ _ _ hτ (hsplit w hw))))
  · refine hPol E Ω l ι n r hr.cont hr.ss ?_
    filter_upwards [hev, (conjSrc_injective (IsCMField.complexConj E).toRingEquiv).tendsto_cofinite.eventually hev]
      with w ⟨hw, _⟩ ⟨hw', S, hS'⟩
    refine ⟨satTot (Bc.cPl w) d S, ?_, hF _ hw' S hS'⟩
    rw [← (hConj E w).2 c d S]
    exact hF w hw _ fun i => (hConj E w).1 _ (P i) (hP.csd i) _ (hS' i)
  · refine hIrr E Ω l ι n hn π hπ c a d hsum P ρ m hP (hi hirr).1 (fun i => (hi₁ i ((hi hirr).2 i)).1) r hr.ss ?_
    filter_upwards [hev] with w ⟨hw, S, hS'⟩
    exact ⟨S, hS', hF w hw S hS'⟩

theorem UpperTheory.V.Af.galUnitary :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.GalUnitary := fun H =>
  assemble H (UpperTheory.sum_family_of_reductions (UpperTheory.sum_two_of_hodge_tate H UpperTheory.galoisRep_direct_sum_away_from_places UpperTheory.sum_hodge_tate) UpperTheory.finiteSum_reduction)
    (UpperTheory.half_of_compatible_polarization H UpperTheory.eta_condition UpperTheory.twist_local_components_compatible (UpperTheory.compatible_polarization_of_link H (compatCsd H) (UpperTheory.satake_galois_compatibility_of_hecke_eigensystem H)))
    UpperTheory.speh_parameter_strings UpperTheory.building_component_uniqueness (UpperTheory.total_reciprocity H) (UpperTheory.total_frobenius_compatibility H) (UpperTheory.twistedDual_frobenius_compatibility (isoOfFrob H.toClassicalTheorems))
    (UpperTheory.satake_galois_compatibility_of_hecke_eigensystem H) UpperTheory.satake_parameters_complex_conjugate (UpperTheory.irreducible_case H)
end
end

section

open NumberField Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp GlobalTheory.HeckeGal

theorem UpperTheory.V.Af.csdOf :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.CsdOf := by
  intro hP F₀ F Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n hn r c P hc haut hpair
  obtain ⟨π, hreg, hatt⟩ := ((UpperTheory.V.Af.autBridge hP F Ω l ι n r).2.1).1 haut
  haveI : IsAlgClosure (maximalRealSubfield F) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans (maximalRealSubfield F) F Ω⟩
  obtain ⟨art, hart⟩ : ∃ art : Neutral.B1.Ideles (maximalRealSubfield F) →* Gab (maximalRealSubfield F) Ω,
      IsGlobalArtin art := hP.toClassicalTheorems.litN.aut.art _ Ω
  have h1 : IsLAdicCharOf (E := F) (Ω := Ω) ι 1 1 := by
    refine ⟨continuous_const, art, 0, hart, fun k _ => ?_, fun x σ _ => ?_⟩
    · simp [HChar.inf]
    · rw [infPow_zero, lPow_zero]
      change (1 : Qbar l) = ι.symm (1 * 1⁻¹) * 1
      simp
  obtain ⟨j, hj⟩ := hc
  let c' : G (maximalRealSubfield F) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap F Ω))
  have hd := UpperTheory.V.Af.selfDualC hP F Ω l ι n hn r π hatt 1 1 h1 c' P ⟨j, hj⟩ (by
    intro s s' hs
    rw [MonoidHom.one_comp, mul_one]
    refine hpair s s' (AlgEquiv.ext fun x => ?_)
    exact DFunLike.congr_fun hs x)
  rw [map_one, GlobalTheory.ContraPair.dualIsConjBy_one] at hd
  exact ⟨π, hreg, hd, hatt⟩
end

section

open NumberField GlobalTheory.CuspRep UpperTheory.V

open GroundTheory.Automorphic in
private theorem lieMatch : UpperTheory.V.Af.Gk.LieMatch := by
  intro F _ _ _ a
  refine ⟨(Fb.lieEq F a).toLinearMap, Subtype.ext ?_, fun X φ _ =>
    congrArg Subtype.val (UpperTheory.V.Af.CuspFin.uAction_lieEq X φ)⟩
  rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← Fb.lieEq_oneL]
  rfl

theorem UpperTheory.V.Af.gelfandKazhdanReal :
    UpperTheory.V.Published.StrongMultOneReal → UpperTheory.V.Published.GelfandKazhdanReal :=
  Gk.gelfandKazhdan_of Gk.conjSub Gk.satConj Gk.satAE Gk.unitTwist Gk.pairOfTwist Gk.pairZero
    (Gk.hermEx_of (fun _ _ _ _ _ => CuspFin.mem_cuspForms_of) lieMatch)
end
