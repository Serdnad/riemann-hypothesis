module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle825
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle696
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle847
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle559
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle845
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle741
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle698
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle842
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertDict

theorem satake_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → (π.SphAt v → IsUnramU U w) ∧ ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → (∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ) ∧ ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), Dv.σw = s → Dv.ϖ = ϖ → NG.SatAt π Dv α → ∃ α' : Fin (n / 2) → ℂˣ, (∀ i, (α' i : ℂ) = α i) ∧ HasSatAt U w s ϖ q α' := by
  intro L _ _ _ n F π U hD v w hO
  refine ⟨GlobalTheory.T.isUnramified_of_sphericalVector_dictionary L n F π U hD v w hO, fun s ϖ q hs hU => ?_⟩
  obtain ⟨hun, hns, hq⟩ := GlobalTheory.T.inert_of_unramifiedIsometricInvolution L v w hO s ϖ q hs hU
  refine ⟨GlobalTheory.T.exists_inertDatum_of_involution_uniformizer L n v w hO hun hns s ϖ hs (hq ▸ hU), fun Dv α hσ hϖ hsat => ?_⟩
  have hsph : π.SphAt v := by
    obtain ⟨f, hf, hf0, U0, hU0, hU0', -⟩ := hsat
    exact ⟨f, hf, hf0, fun κ hκ ht => hU0 κ ((hU0' κ ht).2 hκ)⟩
  obtain ⟨α0, h0⟩ := GlobalTheory.T.exists_satakeParameter_of_unramified_inert_definiteUnitary L n U hD.1 w hun hns s ϖ q hs hU (GlobalTheory.T.isUnramified_of_sphericalVector_dictionary L n F π U hD v w hO hsph)
  subst hσ hϖ hq
  have heq := GlobalTheory.T.inertSatake_heckeEigenvalues_algebraic_automorphic L n F π U hD v w hO Dv α hsat α0 h0
  have hnz := GlobalTheory.T.satakeParameter_ne_zero_of_sameTransform (w.adicCompletion L) Dv.ϖ Dv.σw _ n hU α α0 heq
  refine ⟨fun i => Units.mk0 (α i) (hnz i), fun i => rfl, ?_⟩
  obtain ⟨b, hb, hb2, p, hp, σ, hc, hs1, hs2⟩ := h0
  refine ⟨b, hb, hb2, p, hp, σ, hc, hs1, fun x hx hx0 => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hs2 x hx hx0
  refine ⟨a1, a2, fun h hh => ?_⟩
  rw [a3 h hh, ← heq h hh]
  rfl

end GlobalTheory.InertDict
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.ExportSeries.SpecGood

variable {D : D7}

theorem infPart_eq_zero_of_isIdemAt : ∀ (D : D7) (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 := by
  intro D P e h
  obtain ⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩ := h
  have k1 := congrArg (infPart D) h1
  have k2 := congrArg (infPart D) h2
  have k3 := congrArg (infPart D) h3
  simp only [RingHom.map_mul, RingHom.map_add (f := _), RingHom.map_zero] at k1 k2 k3
  have k4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    simp [infPart, Algebra.TensorProduct.algebraMap_apply]
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [k4] at k3
  linear_combination -k1 + infPart D e * k3 - k2

theorem finUnit_of_res (P : Pl D.host.E) (hP : Formalism.L2.NTheta.IsIdemAt (idemAt P) P) (x : (AE D)ˣ)
    (h1 : (1 - idemAt P) * (x : AE D) = 1 - idemAt P)
    (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (v : (kP P)ˣ)
    (hv : resS D.host.F P ⟨_, hx⟩ = v) :
    infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  obtain ⟨ι, i1, i2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  refine ⟨?_, GlobalTheory.T.finite_part_integral_unit_of_unit_residue D ι i1 i2 P (idemAt P) (GlobalTheory.T.place_idempotent_finite_adele_zero_elsewhere D ι i1 i2 P _ hP) x h1 hx v hv⟩
  have := congrArg (infPart D) h1
  rwa [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, infPart_eq_zero_of_isIdemAt D P _ hP, sub_zero, one_mul] at this

variable {C A : Type} [AddCommGroup C] [CommGroup A]

theorem idemAt_mul_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * idem Q = idemAt P :=
  GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hP

theorem idemAt_mul_conj_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * cA D (idem Q) = 0 := by

  rw [idem, map_sum, Finset.mul_sum]
  exact Finset.sum_eq_zero fun j hj => h.mul_conj hP hj

theorem delQ_eq_one {u : UnivTwist D C} {Q : Finset (Pl D.host.E)} {x : (AE D)ˣ} (hx : ∀ P ∈ Q, u.del P x = 1) :
    u.delQ Q x = 1 := by
  ext PP
  exact congrArg Multiplicative.toAdd (hx PP.1 PP.2)


open Classical in
theorem spec_good (D : D7) (C A : Type) [AddCommGroup C] [CommGroup A] (u : UnivTwist D C) (Q : Finset (Pl D.host.E))
    (χ : Multiplicative (↥Q → C) →* A) (h : u.Good Q) : (u.spec Q χ).Good := by
  have cc := GlobalTheory.DualPairCheck.cA_cA (D := D)
  refine ⟨?_, ?_, ?_, h.1, ?_, ?_⟩
  · haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
    let H : Subgroup (AE D)ˣ := ⨅ P : ↥Q, (u.del P.1).ker
    have hH : IsOpen (H : Set (AE D)ˣ) := by
      rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun P => (h.2 P.1 P.2).isOpen
    refine Subgroup.isOpen_mono (fun x hx => ?_) hH
    rw [Subgroup.mem_iInf] at hx
    show χ (u.delQ Q x) = 1
    rw [delQ_eq_one fun P hP => hx ⟨P, hP⟩, map_one]
  · intro x
    show χ (u.delQ Q _) = 1
    rw [delQ_eq_one fun P hP => (h.2 P hP).rat x, map_one]
  · intro a
    show χ (u.delQ Q _) = 1
    rw [h.delQ_real a, map_one]
  · intro x h1 h2 h3 h4
    show χ (u.delQ Q x) = 1
    replace h4 : (idem Q + cA D (idem Q)) * (x : AE D) = idem Q + cA D (idem Q) := h4
    refine (congrArg χ (delQ_eq_one fun P hP => ?_)).trans (map_one χ)
    refine (h.2 P hP).unram x h1 h2 h3 ?_
    show (idem {P} + cA D (idem {P})) * (x : AE D) = idem {P} + cA D (idem {P})
    have e1 : idem ({P} : Finset (Pl D.host.E)) = idemAt P := Finset.sum_singleton _ _
    rw [e1]
    have k1 := idemAt_mul_idem h.1 hP
    have k2 := idemAt_mul_conj_idem h.1 hP
    have k3 : cA D (idemAt P) * idem Q = 0 := by
      have := congrArg (cA D) k2
      rwa [RingHom.map_mul, cc, RingHom.map_zero] at this
    have k4 : cA D (idemAt P) * cA D (idem Q) = cA D (idemAt P) := by
      rw [← RingHom.map_mul, k1]
    linear_combination (idemAt P + cA D (idemAt P)) * h4 + (1 - (x : AE D)) * (k1 + k2 + k3 + k4)
  · intro PP hPP x h1 hx v hv
    show χ (u.delQ Q x) = (u.spec Q χ).res PP v
    rw [show (u.spec Q χ).res PP = χ.comp ((AddMonoidHom.toMultiplicative (AddMonoidHom.single (fun _ : ↥Q => C) ⟨PP, hPP⟩)).comp
      (u.kap PP)) from dif_pos hPP, MonoidHom.comp_apply]
    have hfu := finUnit_of_res PP (h.1.isIdemAt hPP) x h1 hx v hv
    refine congrArg χ ?_
    ext ⟨P', hP'⟩
    by_cases hne : P' = PP
    · subst hne
      have := (h.2 P' hP').res P' (Finset.mem_singleton_self _) x h1 hx v hv
      simp [UnivTwist.delQ, this]
    · have hd : u.del P' x = 1 := by
        refine (h.2 P' hP').unram x hfu.1 hfu.2.1 hfu.2.2 ?_
        show (idem {P'} + cA D (idem {P'})) * (x : AE D) = idem {P'} + cA D (idem {P'})
        have e1 : idem ({P'} : Finset (Pl D.host.E)) = idemAt P' := Finset.sum_singleton _ _
        rw [e1]
        have z1 : idemAt P' * idemAt PP = 0 := h.1.mul_eq_zero hP' hPP (Ne.symm hne)
        have z2 : idemAt PP * cA D (idemAt P') = 0 := h.1.mul_conj hPP hP'
        linear_combination (idemAt P' + cA D (idemAt P')) * h1 + ((x : AE D) - 1) * (z1 + z2)
      simp [UnivTwist.delQ, hd, Pi.single_apply, hne]
      intro e
      exact absurd (congrArg Subtype.val e) hne

end GlobalTheory.ExportSeries.SpecGood
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist

theorem isResAt_one_of_unram : ∀ (D : D7) (M : Type) [CommGroup M] (χ : (AE D)ˣ →* M) (Q P : Finset (Pl D.host.E)), UnramOutside χ Q → SplitSet P → Q ⊆ P → ∀ PP ∈ P, PP ∉ Q → IsResAt χ PP 1 := by
  intro D M _ χ Q P hχ hP hQ PP hPP hn x hoff hi u hu
  have he : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP := hP.isIdemAt hPP
  have hinf : infPart D (idemAt PP) = 0 :=
    GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨idemAt, by simpa using he, by simp⟩, he.1.2.1⟩
  obtain ⟨hei, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP he
  have hx : (x : AE D) = (1 - idemAt PP) + idemAt PP * (x : AE D) := by
    linear_combination hoff
  have hxI : (⟨_, hi⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = (1 - ⟨_, hei⟩) + ⟨_, hei⟩ * ⟨_, hi⟩ := by
    apply Subtype.ext
    have := congrArg (toEAf D) hx
    simp only [map_add (f := _), map_sub, map_mul, map_one] at this
    exact this.trans rfl

  have hres : ∀ PP' : Pl D.host.E, resS D.host.F PP' ⟨_, hi⟩ ≠ 0 := by
    intro PP'
    by_cases hq : PP' = PP
    · subst hq
      rw [hu]
      exact u.ne_zero
    · have := PP'.isPrime
      have hr0 : resS D.host.F PP' ⟨_, hei⟩ = 0 := by
        have hnle : ¬ PP'.asIdeal ≤ PP.asIdeal := fun hle =>
          hq (HeightOneSpectrum.ext (PP'.isMaximal.eq_of_le PP.isPrime.ne_top hle))
        obtain ⟨a, ha', ha⟩ := SetLike.not_le_iff_exists.1 hnle
        have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ zero_mem _)
        have ha0' : (a : D.host.E) ≠ 0 := fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
        have hint : finPart D (idemAt PP * incA D ((a : D.host.E)⁻¹)) ∈ intAE D := by
          by_contra k
          exact ha ((he.2 a ha0).2 k)
        have hint' := GlobalTheory.IdemRes.toEAf_mem_of_finPart hint
        have hb : toEAf D (incA D (a : D.host.E)) =
            ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
        have hm : (⟨_, hei⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hint'⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E a := by
          apply Subtype.ext
          change toEAf D (idemAt PP) = toEAf D (idemAt PP * incA D ((a : D.host.E)⁻¹)) * _
          rw [← hb, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ ha0', RingHom.map_one, mul_one]
        rw [hm, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha', mul_zero]
      rw [hxI, map_add (f := _), map_sub, map_mul, hr0, map_one, zero_mul, sub_zero, add_zero]
      exact one_ne_zero
  obtain ⟨w, hw⟩ := Formalism.L2.DIV.isUnit_of_resS_ne_zero D.sp.cm ⟨_, hi⟩ hres
  have hinv : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
      Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    have h1 : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * toEAf D (x : AE D) = 1 := by
      rw [← RingHom.map_mul, Units.inv_mul, RingHom.map_one]
    have h2 : toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = 1 := by
      have := congrArg Subtype.val (Units.mul_inv w)
      rw [hw] at this
      exact this
    calc _ = toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * (toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)) := by rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have hl : IsLocUnit PP u x := by
    refine ⟨hoff, ?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hi, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_, hi, hu⟩
    · have := congrArg (infPart D) hx
      rw [map_add (f := _), map_sub, map_mul, map_one, hinf, zero_mul, sub_zero, add_zero] at this
      exact this
    · rw [hinv]
      exact Subtype.property _
  rw [hl.eq_one hχ hP hQ hPP hn, MonoidHom.one_apply]

end GlobalTheory.ConjTwist
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.TwistDetStab

open Classical

variable {D : D7}

theorem infPart_idemAt (P : Pl D.host.E) (e : AE D) (h : Formalism.L2.NTheta.IsIdemAt e P) : infPart D e = 0 := by
  obtain ⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩ := h
  have k1 := congrArg (infPart D) h1
  have k2 := congrArg (infPart D) h2
  have k3 := congrArg (infPart D) h3
  simp only [RingHom.map_mul, RingHom.map_add (f := _), RingHom.map_zero] at k1 k2 k3
  have k4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    simp [infPart, Algebra.TensorProduct.algebraMap_apply]
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [k4] at k3
  linear_combination -k1 + infPart D e * k3 - k2

theorem idemAt_mul_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * idem Q = idemAt P :=
  GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hP

theorem idem_mul_self {Q : Finset (Pl D.host.E)} (h : SplitSet Q) : idem Q * idem Q = idem Q := by
  show (∑ P ∈ Q, idemAt P) * idem Q = idem Q
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun P hP => idemAt_mul_idem h hP

theorem idem_mul_idem_of_disjoint {Q s s' : Finset (Pl D.host.E)} (h : SplitSet Q) (hs : s ⊆ Q) (hs' : s' ⊆ Q)
    (hd : Disjoint s s') : idem s * idem s' = 0 := by
  rw [idem, idem, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
    h.mul_eq_zero (hs hi) (hs' hj) fun e => Finset.disjoint_left.1 hd hi (e ▸ hj)

theorem idem_mul_conj {Q s s' : Finset (Pl D.host.E)} (h : SplitSet Q) (hs : s ⊆ Q) (hs' : s' ⊆ Q) :
    idem s * cA D (idem s') = 0 := by

  rw [idem, idem, map_sum, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => h.mul_conj (hs hi) (hs' hj)

theorem val_mul (d e₁ e₂ : AE D) (h : e₁ * e₂ = 0) :
    (e₁ * d + (1 - e₁)) * (e₂ * d + (1 - e₂)) = (e₁ + e₂) * d + (1 - (e₁ + e₂)) := by
  linear_combination (d * d - 2 * d + 1) * h

theorem prod_val (d : AE D) {Q : Finset (Pl D.host.E)} (h : SplitSet Q) :
    ∀ s ⊆ Q, ∏ P ∈ s, (idemAt P * d + (1 - idemAt P)) = idem s * d + (1 - idem s) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    rw [Finset.prod_insert ha, ih ((Finset.subset_insert a s).trans hs)]
    have e1 : idem (insert a s) = idemAt a + idem s := Finset.sum_insert ha
    rw [e1]
    refine val_mul d _ _ ?_
    have := idem_mul_idem_of_disjoint h (s := {a}) (s' := s)
      (Finset.singleton_subset_iff.2 (hs (Finset.mem_insert_self a s))) ((Finset.subset_insert a s).trans hs)
      (Finset.disjoint_singleton_left.2 ha)
    rwa [show idem ({a} : Finset (Pl D.host.E)) = idemAt a from Finset.sum_singleton _ _] at this

theorem detChar_eq_prod_res : ∀ {D : D7} {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A), t.Good →
    ∀ (β : GL (Fin V.rank) (Lev.EAf D)) {Q' : Finset (Pl D.host.E)}, SplitSet Q' → t.Q ⊆ Q' → ∀ {κ : GA D V},
    κ ∈ GfC V → Lev.finE V κ ∈ St β → SuppAt (idem Q') V κ →
    detChar V t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  intro D V A _ t ht β Q' hQ' hsub κ _ hst hsupp
  have he : idem Q' * idem Q' = idem Q' := idem_mul_self hQ'
  have hce : idem Q' * cA D (idem Q') = 0 := hQ'.isIdemSum.2
  have hroot : IsDetRoot V κ (GlobalTheory.VecInv.detAt (idem Q') he V κ) := by
    have hx : IsDetAt (idem Q') V κ (GlobalTheory.VecInv.detAt (idem Q') he V κ) := GlobalTheory.VecInv.isDetAt_detAt _ he V κ
    unfold IsDetAt at hx
    unfold IsDetRoot
    rw [hx]
    exact idempotent_det_conj_identity (cA D) (idem Q') he hce (mt V κ) hsupp (det_conj_mul V κ)
  rw [detChar_eq ht.real hroot]
  have hR : Q' \ t.Q ⊆ Q' := Finset.sdiff_subset
  have heR : idem (Q' \ t.Q) * idem (Q' \ t.Q) = idem (Q' \ t.Q) := idem_mul_self (hQ'.mono hR)
  have hPi : ∀ P ∈ t.Q, idemAt P * idemAt P = idemAt P := fun P hP => (hQ'.isIdemAt (hsub hP)).1.1
  have hsum : idem (Q' \ t.Q) + idem t.Q = idem Q' := Finset.sum_sdiff hsub
  have hRQ : idem (Q' \ t.Q) * idem t.Q = 0 := idem_mul_idem_of_disjoint hQ' hR hsub Finset.sdiff_disjoint
  have hsplit : GlobalTheory.VecInv.detAt (idem Q') he V κ = GlobalTheory.VecInv.detAt (idem (Q' \ t.Q)) heR V κ *
      ∏ P ∈ t.Q.attach, GlobalTheory.VecInv.detAt (idemAt P.1) (hPi P.1 P.2) V κ := by
    ext
    rw [Units.val_mul, Units.coe_prod]
    show idem Q' * (mt V κ).det + (1 - idem Q') = (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) *
      ∏ P ∈ t.Q.attach, (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1))
    rw [Finset.prod_attach t.Q (fun P => idemAt P * (mt V κ).det + (1 - idemAt P)),
      prod_val _ ht.split t.Q (Finset.Subset.refl _), val_mul _ _ _ hRQ, hsum]
  have hw : t.chi (GlobalTheory.VecInv.detAt (idem (Q' \ t.Q)) heR V κ) = 1 := by
    refine ht.unram _ ?_ (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.StabDet.toEAf_detAt_mem hst _ heR))
      (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.StabDet.toEAf_detAt_inv_mem hst _ heR)) ?_
    · have hinf : infPart D (idem (Q' \ t.Q)) = 0 := by

        rw [idem, map_sum]
        exact Finset.sum_eq_zero fun P hP => infPart_idemAt P _ (hQ'.isIdemAt (hR hP))
      show infPart D (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) = 1
      rw [map_add (f := _), map_mul, map_sub, map_one, hinf]
      ring
    · have a1 : idem t.Q * idem (Q' \ t.Q) = 0 := idem_mul_idem_of_disjoint hQ' hsub hR Finset.disjoint_sdiff
      have a2 : idem (Q' \ t.Q) * cA D (idem t.Q) = 0 := idem_mul_conj hQ' hR hsub
      show (idem t.Q + cA D (idem t.Q)) * (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) =
        idem t.Q + cA D (idem t.Q)
      linear_combination ((mt V κ).det - 1) * (a1 + a2)
  rw [hsplit, map_mul, hw, one_mul, map_prod,
    ← Finset.prod_attach t.Q (fun PP => t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))))]
  refine Finset.prod_congr rfl fun P _ => ?_
  refine ht.res P.1 P.2 _ ?_ (GlobalTheory.StabDet.toEAf_detAt_mem hst _ (hPi P.1 P.2)) _
    (GlobalTheory.StabDet.res_detAt hst _ (hPi P.1 P.2) P.1 (hQ'.isIdemAt (hsub P.2))).symm
  show (1 - idemAt P.1) * (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1)) = 1 - idemAt P.1
  linear_combination (1 - (mt V κ).det) * hPi P.1 P.2

end GlobalTheory.TwistDetStab

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.breuilKisin_lattice_stable_and_hodgeTate_jumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) ∧ ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  first | exact @GlobalTheory.NgalFil.ENStable_and_jumps | exact GlobalTheory.NgalFil.ENStable_and_jumps | (intros; apply GlobalTheory.NgalFil.ENStable_and_jumps <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_stratified_phiModule_crystalline_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : Seed bk d ρ τ), Height s → ∃ (S : Strat bk d) (T : Matrix (Fin d) (Fin d) (WCb l)), MReal S ρ T := by
  first | exact @GlobalTheory.BSP.exists_strat_mreal | exact GlobalTheory.BSP.exists_strat_mreal | (intros; apply GlobalTheory.BSP.exists_strat_mreal <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseLiftWeight

theorem c_eq {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)}
    (hL : L.Is μ0) (hB : B.Good) (hmu : B.mu0 = L.mu0 ((j : ℕ) + 1)) (τ : D.what₂.Tau) :
    B.w.c τ = GlobalTheory.ConjTwist.liftC D j τ := by
  have h1 := hB.inf τ
  rw [hmu] at h1
  have h2 := GlobalTheory.Mem.HeckeExp.hasInfExp_unique h1 (GlobalTheory.ConjRefChar.reference_lift_character_exponent_neg_base hL j τ)
  have hs := hB.sig τ
  have hp : B.w.p τ = ((Wc D j).sig (tauE D τ)).1 := congrArg Prod.fst hs
  have hq : B.w.q τ = ((Wc D j).sig (tauE D τ)).2 := congrArg Prod.snd hs
  have h3 := GlobalTheory.ConjTwist.liftC_cast D j τ
  rw [hp, hq] at h2
  have h4 : (B.w.c τ : ℚ) = (GlobalTheory.ConjTwist.liftC D j τ : ℚ) := by
    rw [h3]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS, GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS] at *
    linarith
  exact_mod_cast h4

theorem lam_eq : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), L.Is μ0 → B.Good → B.mu0 = L.mu0 ((j : ℕ) + 1) → (∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) → (∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) → B.w.lam = FWT.lamV D j := by
  intro D T0 L μ0 j B hL hB hmu hap ham
  funext τ
  have hs := hB.sig τ
  have hp : B.w.p τ = ((Wc D j).sig (tauE D τ)).1 := congrArg Prod.fst hs
  have hq : B.w.q τ = ((Wc D j).sig (tauE D τ)).2 := congrArg Prod.snd hs
  have hc := c_eq hL hB hmu τ
  have e1 := hB.wt.lam_eq τ
  have e2 := (GlobalTheory.ConjTwist.liftWeight_good D j).lam_eq τ
  rw [hp, hq, hap τ, ham τ, hc] at e1
  have key : (B.w.lam τ).w = (FWT.lamV D j τ).w := funext fun a => (e1 a).trans (e2 a).symm
  generalize B.w.lam τ = x at key
  generalize FWT.lamV D j τ = y at key
  cases x
  cases y
  cases key
  rfl

end GlobalTheory.BaseLiftWeight
end
end
