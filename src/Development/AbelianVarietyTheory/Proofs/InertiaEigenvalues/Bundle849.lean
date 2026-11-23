module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle839
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle500
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle841
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremCHypothesesAdmitted
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdmSelf

theorem not_mem_placesOver_of_normV {D : D7} {l M : ℕ} (hM : 0 < M) {P : Pl D.host.E}
    (h : normV P % (2 * l ^ M) = 1) : P ∉ placesOver D.host.E l := by
  intro hl
  have hmem : ((normV P : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have hn : normV P = Ideal.absNorm P.asIdeal := by
      rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hn]
    exact Ideal.absNorm_mem P.asIdeal
  have hl' : ((l : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hl
  have hdm := Nat.div_add_mod (normV P) (2 * l ^ M)
  rw [h] at hdm
  have hx : ((2 * l ^ M * (normV P / (2 * l ^ M)) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    push_cast
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hM
    rw [hk, pow_succ]
    exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_left _ (P.asIdeal.mul_mem_left _ hl'))
  have h1 : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
    have : (1 : 𝓞 D.host.E) = ((normV P : ℕ) : 𝓞 D.host.E) - ((2 * l ^ M * (normV P / (2 * l ^ M)) : ℕ) : 𝓞 D.host.E) := by
      generalize normV P / (2 * l ^ M) = q at hdm ⊢
      rw [← hdm]
      push_cast; ring
    rw [this]
    exact P.asIdeal.sub_mem hmem hx
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

end GlobalTheory.AdmSelf

namespace GlobalTheory.AdmSelf

theorem admissibleConjugatePairPlaces_eq_self_of_goodChar : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ)
    (Q : Finset (Pl D.host.E)) (d : PlE D.host → (G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)))),
    (∀ P ∈ Q, IsSplitPl D.host P) → (∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q) →
    (∀ P ∈ Q, GlobalTheory.TwSys.GoodChar X i M P (d P) ∧ normV P % (2 * X.l i ^ M) = 1) →
    (0 < M ∨ ∀ P ∈ Q, P ∉ placesOver D.host.E (X.l i)) → admissibleConjugatePairPlaces X i Q M = Q := by
  intro D N X i M Q d hs hc hg hl
  classical
  have hnl : ∀ P ∈ Q, P ∉ placesOver D.host.E (X.l i) := fun P hP =>
    hl.elim (fun hM => not_mem_placesOver_of_normV hM (hg P hP).2) fun h => h P hP
  have hchar : ∀ P ∈ Q, ∃ χ : G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)),
      IsOpen (χ.ker : Set (G D.host.E N.Om)) ∧ AntiHom X.cc χ ∧
      (∀ w ∈ placesOver D.host.E (X.l i), ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
        ∀ σ ∈ Dec (F := D.host.E) A, χ σ = 1) ∧
      (∀ w : PlE D.host, w ≠ P → ¬ IsConjPl D.host P w → ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
        ∀ σ ∈ Ine (F := D.host.E) A, χ σ = 1) ∧
      ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (χ σ) := fun P hP => by
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, -⟩ := hg P hP
    refine ⟨d P, h1, h2, h3, fun w a c => h4 w (fun t => t.elim a c), fun A hA x => ?_⟩
    obtain ⟨σ, hσ, hx⟩ := h5 P (Or.inl rfl) A hA (Multiplicative.ofAdd x)
    exact ⟨⟨σ, hσ⟩, congrArg Multiplicative.toAdd hx⟩
  refine Finset.Subset.antisymm (admissibleConjugatePairPlaces_subset i Q M) fun P hP => ?_
  obtain ⟨P', hPP'⟩ := GlobalTheory.TwistDet.exists_isConjPl P
  have hP' : P' ∈ Q := hc P hP P' hPP'
  refine mem_admissibleConjugatePairPlaces_iff.2 ⟨hP, P', hP', hPP', fun w hw => ?_, fun w hw => ?_⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨hs _ hP, hnl _ hP⟩
    · obtain rfl := Finset.mem_singleton.1 hw
      exact ⟨hs _ hP', hnl _ hP'⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨⟨P', by simp, hPP'⟩, hchar _ hP⟩
    · obtain rfl := Finset.mem_singleton.1 hw
      exact ⟨⟨P, by simp, GlobalTheory.GalChar.isConjPl_symm hPP'⟩, hchar _ hP'⟩

end GlobalTheory.AdmSelf
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical



namespace GlobalTheory.ConjHalfSplitInt

theorem frMapAdj_int_iff : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → (IsIntM (frMapAdj S T βS βT x) ↔ IsIntM (frMapAdj S T βS βT (cA D eg • x)) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := by
  intro D S T βS βT Pg Q eg eQ hg hQ _ _ x hx
  have hx' : cA D (eg + eQ) • x = x := (GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_iff' _ _).1 hx
  have hsplit : x = cA D eg • x + cA D eQ • x := by rw [← add_smul, ← map_add (f := _), hx']
  have hA : ∀ e : AE D, frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := fun e => by
    rw [GlobalTheory.RedHalfDrop.frMapAdj_smul_eq, Formalism.L2.Theta.cA_cA]
  have hint : ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P →
      toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun e P h => by
    rw [← GlobalTheory.ExportSeries.idem_eq h]
    unfold GlobalTheory.ExportSeries.idem

    rw [map_sum]
    exact sum_mem fun PP hPP => GlobalTheory.RedHalfDrop.int_idemAt ⟨e, h⟩ hPP
  constructor
  · intro h
    rw [hA, hA]
    exact ⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hg) (h i j),
      fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hQ) (h i j)⟩
  · rintro ⟨h1, h2⟩
    rw [hsplit, GlobalTheory.PlaceVec.frMapAdj_add]
    intro i j
    rw [Matrix.add_apply]
    exact add_mem (h1 i j) (h2 i j)

end GlobalTheory.ConjHalfSplitInt
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.IdemResLift



theorem exists_int_lift : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → ∀ Y : ∀ PP : Pl D.host.E, kP PP, ∃ N : EAf D, ∃ hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (∑ PP ∈ Q, es PP) * N = N ∧ ∀ PP ∈ Q, resS D.host.F PP ⟨N, hN⟩ = Y PP := by
  intro D Q es hI hc Y
  have h1 : ∀ i ∈ Q, es i * es i = es i := fun i hi => (hI i hi).1.1
  have hx := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es Q h1 hc
  have horth : ∀ i ∈ Q, ∀ j ∈ Q, j ≠ i → es i * es j = 0 := fun i hi j hj hji =>
    GlobalTheory.PlaceDatum.idemAt_mul (hI i hi) (hI j hj) (hx i hi j hj) (hx j hj i hi) hji
  have hfix : ∀ j ∈ Q, (∑ i ∈ Q, es i) * es j = es j := by
    intro j hj
    rw [Finset.sum_mul, Finset.sum_eq_single j (fun i hi hij => by rw [mul_comm]; exact horth j hj i hi hij)
      (fun h => absurd hj h), h1 j hj]
  choose a ha using fun P : Pl D.host.E => Ideal.Quotient.mk_surjective (Y P)
  have hint : ∀ P ∈ Q, toEAf D (es P) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun P hP =>
    (GlobalTheory.IdemRes.resS_idem_eq_one D (es P) P (hI P hP)).1
  have hmem : ∀ P ∈ Q, toEAf D (es P) * ((oToS D.host.F D.host.E (a P) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)
      ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun P hP => Subring.mul_mem _ (hint P hP) (Subtype.property _)
  let T : ∀ P, P ∈ Q → Formalism.L2.Herm.intAf D.host.F D.host.E := fun P hP =>
    ⟨toEAf D (es P), hint P hP⟩ * oToS D.host.F D.host.E (a P)
  refine ⟨∑ P ∈ Q, toEAf D (es P) * ((oToS D.host.F D.host.E (a P) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D),
    Subring.sum_mem _ hmem, ?_, ?_⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [← mul_assoc, ← RingHom.map_mul (toEAf D), hfix P hP]
  · intro P hP
    have hN : (⟨_, Subring.sum_mem _ hmem⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ x ∈ Q.attach, T x.1 x.2 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact (Finset.sum_attach Q (fun P => toEAf D (es P) *
        ((oToS D.host.F D.host.E (a P) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D))).symm

    rw [hN, map_sum, Finset.sum_eq_single ⟨P, hP⟩]
    · obtain ⟨h, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (es P) P (hI P hP)
      show resS D.host.F P (⟨toEAf D (es P), hint P hP⟩ * oToS D.host.F D.host.E (a P)) = Y P
      rw [map_mul, resS_oToS, ha, h1, one_mul]
    · rintro ⟨P', hP'⟩ - hne
      have hne' : P' ≠ P := fun h => hne (Subtype.ext h)
      show resS D.host.F P (⟨toEAf D (es P'), hint P' hP'⟩ * oToS D.host.F D.host.E (a P')) = 0
      rw [map_mul, GlobalTheory.TameProd.resS_idem_eq_zero (hI P' hP') hne', zero_mul]
    · intro h; exact absurd (Finset.mem_attach Q _) h

end GlobalTheory.IdemResLift
end
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.wachRelayLemma_arcCoordinateHypotheses : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.RelayArcLifting D HW F ∧ UnusedSlot80.AdmArcA D HW F Cm := by
  first | exact @GlobalTheory.NQ.relay_and_arc_inputs | exact GlobalTheory.NQ.relay_and_arc_inputs | (intros; apply GlobalTheory.NQ.relay_and_arc_inputs <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.localLifting_theoremC_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), RamifiedCoefficientChains.admitted D HW F Cm 10 23 32 32 := by
  first | exact @GlobalTheory.TheoremCAdm.admissible_ranks_of_CMDatum | exact GlobalTheory.TheoremCAdm.admissible_ranks_of_CMDatum | (intros; apply GlobalTheory.TheoremCAdm.admissible_ranks_of_CMDatum <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.localLifting_theoremE_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), WachCoordinates.admitted D HW F Cm 10 := by
  first | exact @GlobalTheory.AdmThmE.admitted_all | exact GlobalTheory.AdmThmE.admitted_all | (intros; apply GlobalTheory.AdmThmE.admitted_all <;> assumption)
end
