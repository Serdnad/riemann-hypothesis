module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.SemistableReduction.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle295
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle254
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle166
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PicardGroup
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
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.RationalIsometry
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.LocalConjugacy

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_congr (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) {r : ℕ} {J J' : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (Jᵀ a b) = Jᵀ b a) (hG' : ∀ a b, cc (J'ᵀ a b) = J'ᵀ b a)
    (hd : J.det ≠ 0) (hd' : J'.det ≠ 0) {L L' : Submodule (𝓞 E) (Fin r → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Jᵀ x y))
    (hsd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', IsIntegral ℤ (herm J'ᵀ x y))
    (hs : ∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (J.map τ) p q ∧ Formalism.UG.HasSignature (J'.map τ) p q) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ ∀ x y, herm Jᵀ (P *ᵥ x) (P *ᵥ y) = herm J'ᵀ x y := by
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram hc
  have hone : ∀ z : E, z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ z := fun z =>
    (FractionalIdeal.mem_one_iff _).trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  obtain ⟨P, hP0, hP⟩ := congr_of_modular (G := Jᵀ) (G' := J'ᵀ) (L := L) (L' := L') (𝔟 := 1)
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt one_ne_zero
    (fun z hz => by
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hz
      exact (FractionalIdeal.mem_one_iff _).2 ⟨IsCMField.ringOfIntegersComplexConj E a, rfl⟩)
    hG hG' (by rwa [Matrix.det_transpose]) (by rwa [Matrix.det_transpose]) hL hL'
    (by simpa only [hone] using hsd) (by simpa only [hone] using hsd')
    (fun τ => by
      obtain ⟨p, q, h, h'⟩ := hs τ
      obtain ⟨f⟩ : Nonempty (Fin r ≃ Fin p ⊕ Fin q) := ⟨h.choose⟩
      obtain ⟨A, hA, e⟩ := GlobalTheory.FlagMeas.exists_congr_of_hasSignature h f
      obtain ⟨A', hA', e'⟩ := GlobalTheory.FlagMeas.exists_congr_of_hasSignature h' f
      refine GlobalTheory.Published.Landherr.congr_of_gram_eq τ hA hA' ?_
      rw [GlobalTheory.Published.gram_eq, GlobalTheory.Published.gram_eq]
      exact e.trans e'.symm)
  exact ⟨P, hP0, fun x y => by rw [herm_mulVec, ← hP]⟩

theorem gram_herm (W : HSpace E) (a b : Fin W.rank) : cc (W.gramᵀ a b) = W.gramᵀ b a :=
  W.herm.eq (W.frame b) (W.frame a)

theorem exists_isometry (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W Y : HSpace E) (hW : W.SigOK) (hY : Y.SigOK)
    (hr : W.rank = Y.rank) (hs : ∀ τ, W.sig τ = Y.sig τ) :
    ∃ φ : W.V ≃ₗ[E] Y.V, HSpace.IsIsomEmb W Y φ.toLinearMap := by
  obtain @⟨V, i1, i2, i3, i4, i5, hT, hh, hn, r, hrk, fr, sg, L, hL, hu⟩ := Y
  change W.rank = r at hr
  subst hr
  let Y : HSpace E := ⟨V, hT, hh, hn, W.rank, hrk, fr, sg, L, hL, hu⟩
  obtain ⟨P, hP0, hP⟩ := exists_congr hc (r := W.rank) (J := Y.gram) (J' := W.gram) (gram_herm Y) (gram_herm W)
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit Y).ne_zero (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W).ne_zero
    (isLattice_coordLat Y Y.L0 Y.standardTuple_isLattice Y.baseLattice_isUnimodular)
    (isLattice_coordLat W W.L0 W.standardTuple_isLattice W.baseLattice_isUnimodular)
    (selfDual_coordLat Y Y.L0 Y.baseLattice_isUnimodular) (selfDual_coordLat W W.L0 W.baseLattice_isUnimodular)
    (fun τ => ⟨_, _, hY τ, by have := hW τ; rwa [hs τ] at this⟩)
  refine ⟨(W.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit))).trans
    Y.frame.equivFun.symm, fun x y => ?_⟩
  change Y.hT (Y.frame.equivFun.symm (P *ᵥ W.frame.equivFun x))
    (Y.frame.equivFun.symm (P *ᵥ W.frame.equivFun y)) = _
  rw [← herm_coord, ← herm_coord, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact hP _ _

end

theorem rationalSt (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D :=
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W Y hW hY hr hs => exists_isometry (E := D.host.E) D.sp.cm.cmUnram W Y hW hY hr hs

end GlobalTheory.RationalIsometry

end
end

section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitPlace

theorem isSplit_of_norm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {p : ℕ} (hp : p.Prime)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal →
      Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 E) ∉ w.asIdeal ^ 2)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (p : 𝓞 F) ∈ v.asIdeal) : IsSplit (E := E) v := by
  classical
  haveI hfin : Module.Finite (𝓞 F) (𝓞 E) := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  haveI hint : Algebra.IsIntegral (𝓞 F) (𝓞 E) := by
    first
    | infer_instance
    | exact Algebra.IsIntegral.of_finite (𝓞 F) (𝓞 E)

  have hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact h2

  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  rw [hdeg] at hsum

  have hover : ∀ Q : Ideal (𝓞 E), Q.LiesOver v.asIdeal → (p : 𝓞 E) ∈ Q := by
    intro Q hQo
    have hmem : (p : 𝓞 F) ∈ Q.under (𝓞 F) := by
      rw [← hQo.over]
      exact hv
    have hmem' : algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ Q := hmem
    simpa using hmem'

  have hf : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.inertiaDeg (𝓞 F) = 1 := by
    rintro ⟨Q, hQp, hQo⟩
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have hN : Ideal.absNorm Q = p := (h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).1
    have key : Ideal.absNorm v.asIdeal ^ Q.inertiaDeg (𝓞 F) = p := by
      rw [Ideal.absNorm_pow_inertiaDeg v.asIdeal Q]
      exact hN
    exact Nat.Prime.eq_one_of_pow (by rw [key]; exact hp)

  have he : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) = 1 := by
    rintro ⟨Q, hQp, hQo⟩
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have hsq : (p : 𝓞 E) ∉ Q ^ 2 := (h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).2
    have hle : Q.ramificationIdx (𝓞 F) ≤ 1 := by
      rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot]
      by_contra hlt
      push_neg at hlt
      have hmap : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q ^ 2 :=
        Ideal.le_pow_of_le_ramificationIdx' hlt
      apply hsq
      have hin := hmap (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hv)
      simpa using hin
    have hpos : 0 < Q.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos (R := 𝓞 F) Q
    show Q.ramificationIdx (𝓞 F) = 1
    omega

  by_contra hns
  obtain ⟨Q0, hQ0p, hQ0o⟩ : ∃ Q0 : Ideal (𝓞 E), Q0.IsPrime ∧ Q0.LiesOver v.asIdeal := by
    first
    | obtain ⟨Q0, hQ0m, hQ0o⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
      exact ⟨Q0, hQ0m.isPrime, hQ0o⟩
    | obtain ⟨Q0, hQ0⟩ := Set.nonempty_of_ncard_ne_zero
        (IsDedekindDomain.primesOver_ncard_ne_zero v.asIdeal (𝓞 E))
      exact ⟨Q0, hQ0.1, hQ0.2⟩
  let q0 : v.asIdeal.primesOver (𝓞 E) := ⟨Q0, hQ0p, hQ0o⟩
  have honly : ∀ q : v.asIdeal.primesOver (𝓞 E), q = q0 := by
    rintro ⟨Q, hQp, hQo⟩
    by_contra hne
    apply hns
    haveI := hQo
    haveI := hQ0o
    refine ⟨⟨Q, hQp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      ⟨Q0, hQ0p, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q0⟩, ?_, hQo.over.symm, hQ0o.over.symm⟩
    intro hPQ
    exact hne (Subtype.ext (congrArg HeightOneSpectrum.asIdeal hPQ))
  rw [Finset.sum_eq_single q0 (fun b _ hb => absurd (honly b) hb)
    (fun h0 => absurd (Finset.mem_univ q0) h0), he q0, hf q0] at hsum
  omega

theorem isSplit_of_splitsCompletely : ∀ (D : D7) (p : ℕ), SplitsCompletely D p → ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal → IsSplit (E := D.host.E) v := by
  intro D p hp v hv
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    first
    | haveI : IsCMField D.host.E := Formalism.HC.HostAx.isCMField_hostE D.host.toHostAx
      exact IsQuadraticExtension.finrank_eq_two _ _
    | have hE := Formalism.HC.HostAx.finrank_cmField D.host.toHostAx
      have hF := Formalism.HC.HostAx.finrank_hostF D.host.toHostAx
      have hm := Module.finrank_mul_finrank ℚ D.host.F D.host.E
      have hpos : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
      rw [hE, hF] at hm
      rw [hF] at hpos
      exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  exact isSplit_of_norm h2 hp.1 hp.2 v hv

end GlobalTheory.SplitPlace
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeTieCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.FWT
  Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

variable {WL : ℕ → Type} [∀ j, AddCommGroup (WL j)] [∀ j, Module D.what₂.LL (WL j)]
  (e : ∀ i : Fin D.R.m, WL ((i : ℕ) + 1) ≃ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL))

theorem isSplitPl_iff (P : PlE D.host) :
    IsSplitPl D.host P ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal := by
  have hc : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (GlobalTheory.SplitOffPlaces.conjSpec P).asIdeal := by
    rw [Formalism.L2.Col.conjIdeal_eq]; rfl
  rw [hc]
  constructor
  · rintro ⟨x, hx, h⟩ he
    refine h (Formalism.L2.Col.cO D.host.E x) (bridge_star_holds D.R D.host _) ?_
    rw [← he] at hx
    exact hx
  · intro hne
    by_contra h
    refine hne (P.isMaximal.eq_of_le (GlobalTheory.SplitOffPlaces.conjSpec P).isPrime.ne_top fun x hx => ?_).symm
    by_contra hx'
    refine h ⟨x, hx, fun y hy hyP => hx' ?_⟩
    have : y = Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext (hy.trans (bridge_star_holds D.R D.host _).symm)
    rw [this] at hyP
    exact hyP

theorem level_notMem {P : PlE D.host} (h : ∃ i', P ∉ D.ntw.S0 i') :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨i', hi⟩ := h
  intro hm
  rw [Nat.cast_mul] at hm
  rcases P.isPrime.mem_or_mem hm with h | h
  · exact hi (D.ntw.placesOver_subset_exceptional i' 0 h)
  · exact hi (D.ntw.placesOver_subset_exceptional i' 1 h)

theorem scalar_eq (i : Fin D.R.m) (P : PlE D.host) (k : ℕ) :
    (((R.C.mu0 i).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹ = heckeScalar R i P k := by
  rw [heckeScalar, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_pow]

theorem exists_family (t : ∀ i : Fin D.R.m, ℕ → PlE D.host → Module.End D.what₂.LL (Fin (R.nW i) → D.what₂.LL)) :
    ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (WL j),
      ∀ (i : Fin D.R.m) k P, (e i).conj (hL ((i : ℕ) + 1) k P) = t i k P := by
  refine ⟨fun j => match j with
    | 0 => fun _ _ => 0
    | n + 1 => fun k P => if h : n < D.R.m then (e ⟨n, h⟩).symm.conj (t ⟨n, h⟩ k P) else 0, fun i k P => ?_⟩
  simp only [dif_pos i.2]
  exact (e i).conj.apply_symm_apply (t i k P)

end Local

section Comparison₂

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  {WL : ℕ → Type} [∀ j, AddCommGroup (WL j)] [∀ j, Module D.what₂.LL (WL j)]
  (e : ∀ i : Fin D.R.m, WL ((i : ℕ) + 1) ≃ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL))

end Comparison₂

end GlobalTheory.HeckeTieCompare
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOverPlace

theorem unrAt_of_unramAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F),
    IsPlaceIdem D v ε → GlobalTheory.WeilParts.UnramAt ε χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E),
    w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w := by
  intro D χ v ε hε hu w hw x hx
  obtain ⟨h1, h2⟩ := (GlobalTheory.LFun.EulerTie.isUnitAt_iff w x).1 hx
  have hc := GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E)
  obtain ⟨k0, k1, -⟩ := GlobalTheory.CMPrimeIdele.place_comp hc hε
  have key : χ (GlobalTheory.LFun.locIdele D.host.F w x) = 1 := by
    refine hu _ ?_ ((GlobalTheory.LFun.EulerTie.locIdele_int_iff w x).2 h1) (by
      rw [← map_inv]; exact (GlobalTheory.LFun.EulerTie.locIdele_int_iff w x⁻¹).2 h2)
    refine hc.ext' ?_ fun Q ↦ ?_
    · have k0' : GlobalTheory.CMPrimeIdele.infPart D.host.F D.host.E (algebraMap (AF D.host.F) (AE D) ε) = 0 := k0
      have k2 : GlobalTheory.CMPrimeIdele.infPart D.host.F D.host.E ((GlobalTheory.LFun.locIdele D.host.F w x : AE D) - 1) = 0 := by
        rw [map_sub, (GlobalTheory.LFun.EulerTie.parts_locIdele w x).1, map_one, sub_self]
      rw [map_mul, k0', zero_mul, k2]
    · rw [GlobalTheory.CMPrimeIdele.ev_mul]
      by_cases hQ : Q = w
      · subst hQ
        rw [k1 Q hw, one_mul]
      · have e : GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E ((GlobalTheory.LFun.locIdele D.host.F w x : AE D) - 1) Q = 0 := by
          rw [map_sub, map_one]
          show GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E (GlobalTheory.LFun.locIdele D.host.F w x : AE D) Q - 1 = 0
          rw [GlobalTheory.LFun.EulerTie.finComp_locIdele_ne hQ, sub_self]
        rw [e, mul_zero]
  show Circle.toUnits (χ (GlobalTheory.LFun.locIdele D.host.F w x)) = 1
  rw [key, map_one]

end GlobalTheory.UnrOverPlace
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramOver

theorem map_eq_one_of_supp {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) {e x : R}
    (hx : e * (x - 1) = x - 1) (he : f e = 0) : f x = 1 := by
  have h := congrArg f hx
  rw [map_mul, map_sub, map_one, he, zero_mul] at h
  exact sub_eq_zero.mp h.symm

theorem val_eq_one_of_unit {R K Γ : Type} [CommRing R] [CommRing K] [LinearOrderedCommMonoidWithZero Γ]
    (w : Valuation K Γ) (f : R →+* K) (x : Rˣ) (a : w (f x) ≤ 1) (b : w (f (x⁻¹ : Rˣ)) ≤ 1) : w (f x) = 1 := by

  have hprod : w (f x) * w (f (x⁻¹ : Rˣ)) = 1 := by
    rw [← Valuation.map_mul, ← map_mul f, Units.mul_inv, map_one f, Valuation.map_one]
  refine le_antisymm a ?_
  calc (1 : Γ) = w (f x) * w (f (x⁻¹ : Rˣ)) := hprod.symm
    _ ≤ w (f x) := mul_le_of_le_one_right' b

theorem unramAt_of_unrAt : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → χ.UnrAt P) → UnramAt ε c := by
  classical
  intro D c χ hce v ε hε hunr x hsupp hxi hxii
  obtain ⟨ι, hι1, hint, happ⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hmain⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι hι1 hint
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι hι1 hint happ) c χ hce
  obtain ⟨α, rfl, -, hα0⟩ := hε

  have hinf0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  have hfin : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by
    show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl

  have hx1 : infPart D (x : AE D) = 1 := map_eq_one_of_supp (infPart D) hsupp hinf0

  have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := fun P =>
    val_eq_one_of_unit Valued.v ((GlobalTheory.CharLocProd.evalAt P).comp (ι.toRingHom.comp (finPart D))) x
      ((hint _).1 hxi P) ((hint _).1 hxii P)

  have hoff : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ≠ v →
      ι (finPart D (x : AE D)) P = 1 := by
    intro P hP
    refine map_eq_one_of_supp ((GlobalTheory.CharLocProd.evalAt P).comp (ι.toRingHom.comp (finPart D))) hsupp ?_
    show ι (finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) P = 0
    rw [hfin]
    have hα : α (P.under (𝓞 D.host.F)) = 0 := hα0 _ hP
    apply GlobalTheory.PlaceIdem.eq_zero_of_val
    intro n
    have h := happ α 0 P n (by rw [hα, map_zero, sub_zero, Valuation.map_zero]; exact zero_le')
    rwa [map_zero, map_zero, sub_zero] at h

  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map (ι.toRingHom.comp (finPart D)).toMonoidHom x)
  have hXP : ∀ P, ((Units.map (ι.toRingHom.comp (finPart D)).toMonoidHom x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) P = ι (finPart D (x : AE D)) P := fun _ => rfl
  have hS2 : ∀ P ∈ S, Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) ∧
      Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
        P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k P : D.host.E) := by
    intro P hP
    have h := hS P hP
    rw [hXP] at h
    exact ⟨h.1, h.2.1⟩
  have hS'2 : ∀ P, P ∉ S → Valued.v (ι (finPart D (x : AE D)) P) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    have h := hS' P hP
    rwa [hXP] at h

  obtain ⟨k', hk'1, hk'2⟩ : ∃ k' : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ,
      (∀ P, P.under (𝓞 D.host.F) = v → k' P = k P) ∧ (∀ P, P.under (𝓞 D.host.F) ≠ v → k' P = 1) :=
    ⟨fun P => if P.under (𝓞 D.host.F) = v then k P else 1, fun _ h => if_pos h, fun _ h => if_neg h⟩
  have hcx := hmain x hx1 S k' ?_ ?_
  · have hprod : ∏ P ∈ S, ((χ.locK P (k' P) : ℂˣ) : ℂ) = 1 := by
      apply Finset.prod_eq_one
      intro P hPS
      by_cases hP : P.under (𝓞 D.host.F) = v
      · rw [hk'1 P hP]
        have hu : χ.loc P (atFin P (k P)) = 1 := by
          apply hunr P hP
          show Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k P : D.host.E)) = 1
          rw [GlobalTheory.CharLocProd.val_algebraMap, ← (hS2 P hPS).1]
          exact hval P
        show ((χ.loc P (atFin P (k P)) : ℂˣ) : ℂ) = 1
        rw [hu, Units.val_one]
      · rw [hk'2 P hP, map_one, Units.val_one]
    exact Circle.coe_eq_one.mp (hcx.trans hprod)
  · intro P hPS
    by_cases hP : P.under (𝓞 D.host.F) = v
    · rw [hk'1 P hP]
      exact hS2 P hPS
    · rw [hk'2 P hP, hoff P hP]
      refine ⟨?_, ?_⟩
      · rw [Units.val_one, Valuation.map_one, map_one]
      · rw [Units.val_one, map_one, sub_self, Valuation.map_zero]
        exact zero_le'
  · intro P hPS
    exact hS'2 P hPS

end GlobalTheory.UnramOver
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tensorIdeleAbs_det_unitaryAdelic_eq_one : ∀ (D : D7) (W : HSp D) (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 := by
  first | exact @GlobalTheory.UnitaryDetAbs.absE_det_matHom | exact GlobalTheory.UnitaryDetAbs.absE_det_matHom | (intros; apply GlobalTheory.UnitaryDetAbs.absE_det_matHom <;> assumption)
end
