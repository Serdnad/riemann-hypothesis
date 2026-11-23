module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle723
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle539
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle724
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle333
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle715
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle708
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle337
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaleRootsProdIcc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle243
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle389
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle518
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle521
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle725
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle726
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle728
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.CoeffIdeal

theorem principal_of_saturated {S k : Type} [CommRing S] [IsNoetherianRing S] [CommRing k]
    [IsPrincipalIdealRing k] (π : S →+* k) (hπ : Function.Surjective π) (p : S)
    (hker : ∀ x, π x = 0 → p ∣ x) (hp : Ideal.span {p} ≤ Ideal.jacobson ⊥) (P : Ideal S)
    (hP : ∀ x, p * x ∈ P → x ∈ P) : ∃ g, P = Ideal.span {g} := by
  obtain ⟨g', hg'⟩ := (IsPrincipalIdealRing.principal (P.map π)).principal
  have h0 : g' ∈ P.map π := by rw [hg']; exact Submodule.mem_span_singleton_self _
  obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective π hπ).1 h0
  refine ⟨g, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 hg)⟩
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian P) hp fun x hx => ?_
  have h1 : π x ∈ P.map π := Ideal.mem_map_of_mem π hx
  rw [hg'] at h1
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨c, rfl⟩ := hπ c'
  obtain ⟨y, hy⟩ := hker (x - c * g) (by rw [map_sub, map_mul, ← hc', smul_eq_mul, sub_self])
  have hyP : y ∈ P := hP y (hy ▸ P.sub_mem hx (P.mul_mem_left c hg))
  have e : x = c * g + p • y := by rw [smul_eq_mul, ← hy]; ring
  rw [e]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self g))
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self p) hyP)

theorem c_frob_mem {S A : Type} [CommRing S] [IsNoetherianRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    {ι : Type} (TB : TopBasis s I ι) (hI : I ≤ Ideal.jacobson ⊥) (φ : S →+* S) (Φ : A →+* A)
    (hφ : ∀ a, s (φ a) = Φ (s a)) (hφI : I.map φ ≤ I) (x : A) (N : Ideal S) (hN : ∀ i, φ (TB.c i x) ∈ N)
    (j : ι) : TB.c j (Φ x) ∈ N := by
  have hH : IsHausdorff I (S ⧸ N) := IsHausdorff.of_le_jacobson _ _ (by simpa only [Ideal.jacobson_bot] using hI)
  refine Ideal.Quotient.eq_zero_iff_mem.1 (hH.haus _ fun n => ?_)
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset → TB.c i x ∈ I ^ n := fun i hi => by simpa using hi
  have h1 := Ideal.mem_map_of_mem Φ (TB.approx x n _ hF)
  have e : Φ.comp s = s.comp φ := RingHom.ext fun a => (hφ a).symm
  rw [Ideal.map_map, e, ← Ideal.map_map, Ideal.map_pow] at h1
  have h2 := TB.c_mem_of_mem_map _ _ (Ideal.map_mono (Ideal.pow_right_mono hφI n) h1) j

  rw [map_sub, map_sub, map_sum, map_sum] at h2
  have h3 : ∑ i ∈ (TB.fin x n).toFinset, TB.c j (Φ (s (TB.c i x) * TB.b i)) ∈ N :=
    N.sum_mem fun i _ => by
      rw [map_mul, ← hφ, TB.c_mul]
      exact N.mul_mem_right _ (hN i)
  have h4 : Ideal.Quotient.mk N (TB.c j (Φ x)) =
      (TB.c j (Φ x) - ∑ i ∈ (TB.fin x n).toFinset, TB.c j (Φ (s (TB.c i x) * TB.b i))) • (1 : S ⧸ N) := by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]
    simpa using h3
  rw [SModEq.zero, h4]
  exact Submodule.smul_mem_smul h2 Submodule.mem_top

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

theorem prime_l : Prime (l : (Wq l a)⟦X⟧) := by
  have key : ∀ x : (Wq l a)⟦X⟧, (l : (Wq l a)⟦X⟧) ∣ x →
      PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l a)) x = 0 := by
    rintro _ ⟨y, rfl⟩
    rw [map_mul, map_natCast, l_eq_zero, zero_mul]
  refine ⟨l_ne_zero l a, fun h => ?_, fun x y h => ?_⟩
  · have := key 1 h.dvd
    rw [map_one] at this
    exact one_ne_zero this
  · have := key _ h
    rw [map_mul] at this
    exact (mul_eq_zero.1 this).imp (dvd_of_map_eq_zero l a x) (dvd_of_map_eq_zero l a y)

theorem ne_zero_of_isPer {K : FinExt l} (bk : BK K) {τ : Ainf l} (h : bk.IsPer τ) : τ ≠ 0 := by
  rintro rfl
  obtain ⟨-, ε, η, ⟨-, hδ1⟩, h⟩ := h
  rw [map_zero, eq_comm, Units.mul_right_eq_zero, sub_eq_zero] at h
  have h1 : ε = 1 := by
    have := congrArg (fun w : Ainf l => w.coeff 0) h
    simpa using this
  exact hδ1 (by rw [h1, map_one, map_one])

end GlobalTheory.BSP.CoeffIdeal


open GlobalTheory.BSP.CoeffIdeal in
theorem GlobalTheory.BSP.pow_l_mem_span_coeff : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (M : ℕ), ∃ r : ℕ, (l : bk.S) ^ r ∈ Ideal.span (Set.range fun i => TB.c i (τ ^ M)) := by
  intro l _ K bk τ hτ ι TB M
  set I : Ideal bk.S := Ideal.span (Set.range fun i => TB.c i (τ ^ M)) with hI
  have hJ : bk.J ≤ Ideal.jacobson ⊥ := by
    have := bk.complete
    exact IsAdicComplete.le_jacobson_bot _
  have hpr := prime_l l bk.a
  let P : Ideal bk.S :=
    { carrier := {x | ∃ r : ℕ, (l : bk.S) ^ r * x ∈ I}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro x y ⟨r, hr⟩ ⟨t, ht⟩
        refine ⟨r + t, ?_⟩
        have := I.add_mem (I.mul_mem_left ((l : bk.S) ^ t) hr) (I.mul_mem_left ((l : bk.S) ^ r) ht)
        convert this using 1
        ring
      smul_mem' := by
        rintro c x ⟨r, hr⟩
        refine ⟨r, ?_⟩
        rw [smul_eq_mul, mul_left_comm]
        exact I.mul_mem_left c hr }
  have hsat : ∀ x, (l : bk.S) * x ∈ P → x ∈ P := by
    rintro x ⟨r, hr⟩
    exact ⟨r + 1, by rwa [pow_succ, mul_assoc]⟩
  have hIP : I ≤ P := fun x hx => ⟨0, by simpa using hx⟩
  obtain ⟨g, hg⟩ := principal_of_saturated
    (PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)))
    (PowerSeries.map_surjective _ (WittVector.constantCoeff_surjective l)) (l : bk.S)
    (dvd_of_map_eq_zero l bk.a) (le_sup_left.trans hJ) P hsat
  have hgP : g ∈ P := by rw [hg]; exact Ideal.mem_span_singleton_self g
  have hdvd : ∀ i, g ∣ TB.c i (τ ^ M) := fun i => by
    rw [← Ideal.mem_span_singleton, ← hg]
    exact hIP (Ideal.subset_span ⟨i, rfl⟩)
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact pow_ne_zero M (ne_zero_of_isPer l bk hτ) (TB.eq_zero_of_c _ fun i => zero_dvd_iff.1 (hdvd i))
  have hlg : ¬ (l : bk.S) ∣ g := by
    rintro ⟨y, hy⟩
    have h1 : y ∈ P := hsat y (hy ▸ hgP)
    rw [hg, Ideal.mem_span_singleton] at h1
    obtain ⟨z, hz⟩ := h1
    refine hpr.not_unit (IsUnit.of_mul_eq_one z (mul_left_cancel₀ hg0 ?_))
    rw [mul_one]
    conv_rhs => rw [hy, hz]
    ring
  have hφJ : bk.J.map (frobS l bk.a) ≤ bk.J := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]
    refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    obtain ⟨b, hb⟩ := frobS_eq l bk.a bk.E
    rw [hb, add_comm]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (Fact.out : l.Prime).pos)
  have hE : ∀ j, frobS l bk.a g ∣ bk.E ^ M * TB.c j (τ ^ M) := fun j => by
    have := c_frob_mem TB hJ (frobS l bk.a) WittVector.frobenius bk.ev_frob hφJ (τ ^ M)
      (Ideal.span {frobS l bk.a g}) (fun i => Ideal.mem_span_singleton.2 (map_dvd _ (hdvd i))) j
    rwa [map_pow, hτ.1, mul_pow, ← map_pow, TB.c_mul, Ideal.mem_span_singleton] at this
  have hEI : ∀ x ∈ I, frobS l bk.a g ∣ bk.E ^ M * x := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hE i
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact dvd_add hx hy
    | smul c x _ hx => rw [smul_eq_mul, mul_left_comm]; exact hx.mul_left c
  obtain ⟨r, hr⟩ := hgP
  have hlφ : ¬ (l : bk.S) ∣ frobS l bk.a g := by
    obtain ⟨b, hb⟩ := frobS_eq l bk.a g
    rw [hb]
    intro h
    exact hlg (hpr.dvd_of_dvd_pow ((dvd_add_left (dvd_mul_right _ b)).1 h))
  have hfin : frobS l bk.a g ∣ bk.E ^ M * g := by
    obtain ⟨z, hz⟩ := hEI _ hr
    obtain ⟨w, hw⟩ : (l : bk.S) ^ r ∣ z :=
      hpr.pow_dvd_of_dvd_mul_left r hlφ ⟨bk.E ^ M * g, by rw [← hz]; ring⟩
    refine ⟨w, mul_left_cancel₀ (pow_ne_zero r hpr.ne_zero) ?_⟩
    rw [mul_left_comm, hz, hw]
    ring
  have hu := GlobalTheory.T.isUnit_of_frobenius_dvd_eisenstein_pow_mul l K bk g hlg M hfin
  exact ⟨r, (I.mul_unit_mem_iff_mem hu).1 hr⟩
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section
namespace GlobalTheory.UseLocInst



theorem exists_setC : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i), tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π →
    TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i →
    D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d →
    (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool)
      (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ),
        ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      ∃ (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)) (_ : Irreducible lam)
        (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
        (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
        (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
        (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
        SetC HW r ρ π C hA lam θ h w' η typ U := by
  intro D HW F i r ρ π hB3 hJa hGood hZ hG2 hG3 hCont hDec hEps h5 hsm hq hd hPosition w hw
  obtain ⟨C, hA⟩ := GlobalTheory.UseLoc.exists_caseA_enl D i w hw hsm hq hd
  obtain ⟨lam, hlam⟩ := GlobalTheory.UseLocUnif.exists_uniformiser (D.nd.l i) C.LL
  obtain ⟨ep, hJ⟩ := hJa
  have hτ : ∀ a : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)),
      ∃ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, tableLineDegreeTwo.Over (embC HW C hA) a τ ∧
        ∀ τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, tableLineDegreeTwo.Over (embC HW C hA) a τ' → τ' = τ :=
    fun a => GlobalTheory.UseLoc.extendUnramEmb (D.nd.l i) (D.nbr i w hw).Kw C.LL hA.1 (embC HW C hA a)
  choose τa _hτa hτu using hτ
  have hJτ := fun a => hJ i r hGood w hw C (τa a)
  choose gA ρA _hRead hX hW using hJτ
  haveI := (Br.PD D.loc D.nbr i w hw).finK₀
  haveI : NeZero (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨h, w', η, typ, U, hS, hU⟩ := hPosition _ (fun a => decide (AdmissibleParameterJ.TypeU D ep (gA a))) ρA
  obtain ⟨θ, hθc, hθcr, hθj⟩ := (hB3 (D.nd.l i) (D.nbr i w hw).Kw C.LL hA).1 (fun a => (w' a : ℤ))
  have hθj' : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ → ∀ b,
      multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b =
        if b = (w' a : ℤ) then 1 else 0 := hθj
  have hθnz : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ →
      multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ (w' a) ≠ 0 := by
    intro a τ hO
    rw [hθj' a τ hO]
    simp
  have hWp : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ → ∀ b : ℤ,
      multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) τ b =
        ((U a).count (b + w' a) : ℤ) := by
    intro a τ hO b
    rw [hτu a τ hO, ((hW a) ρ π hZ hDec b).2.1]
    obtain ⟨h1, h2⟩ := hU a b
    by_cases hb : ((b : ℤ) : ℚ) ∈ AdmissibleParameterJ.JW D (decide (AdmissibleParameterJ.TypeU D ep (gA a))) (D.nd.j i) (ρA a)
    · rw [if_pos hb, h1.2 hb]
      simp
    · rw [if_neg hb]
      have : (U a).count (b + w' a) ≠ 1 := fun e => hb (h1.1 e)
      omega
  have hL6 := GlobalTheory.UseLoc.crys_Wp_rTw D i r ρ π w hw C hGood hZ hG2 hDec
  have hL4 := GlobalTheory.UseLoc.TwistCrysW.isCrys_and_multV D i w hw C
  have hL5 := GlobalTheory.UseLoc.twistM_repV_cont D i w hw C
  have hWcont : Continuous fun g => WpO D.nd i ρ π g :=
    (GlobalTheory.Pass.stepSub_holds D i r ρ hGood π hDec {π} rfl).1.1
  refine ⟨C, hA, lam, hlam, θ, h, w', η, typ, U, ?_, ?_⟩
  · refine ⟨D.R.t_odd.pos, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Br.PD_p]
      exact hS
    · exact hL5 _ (WpO D.nd i ρ π) θ hWcont hθc
    · exact (hL4 _ (WpO D.nd i ρ π) θ hL6.1 hθcr).1
    · intro a τ hO b
      have e := (hL4 _ (WpO D.nd i ρ π) θ hL6.1 hθcr).2 τ (w' a) (hθnz a τ hO) (b - w' a)
      rw [sub_add_cancel] at e
      rw [e, hWp a τ hO, sub_add_cancel]
    · intro c hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
      obtain ⟨k1, k2, k3⟩ := GlobalTheory.UseLoc.chiT_cont_isCrys_multV D i r ρ π w hw C θ c hc1 hc2 hG2 hθc hθcr
      refine ⟨GlobalTheory.UseLoc.chiT_cyc D i w hw C θ c hc1 hc2, k1, k2, ?_⟩
      intro a τ hO b
      have e := k3 τ (b - ((c : ℤ) - 1))
      rw [sub_add_cancel b ((c : ℤ) - 1)] at e
      rw [e, hθj' a τ hO]
      split_ifs <;> omega
  · intro x
    refine ⟨hL5 _ (rTwO D.nd i r x) θ (GlobalTheory.Pass.FamCont.stepCont D i r hGood x).1 hθc,
      (hL4 _ (rTwO D.nd i r x) θ (hL6.2 x) hθcr).1, ?_,
      GlobalTheory.UseLoc.InstPoly.charpoly_congr D i r ρ π w hw C θ lam hlam hG3 x⟩
    intro a τ hO b
    have e := (hL4 _ (rTwO D.nd i r x) θ (hL6.2 x) hθcr).2 τ (w' a) (hθnz a τ hO) (b - w' a)
    rw [sub_add_cancel] at e
    rw [e, hτu a τ hO, ((hX a) x (b - w' a)).2.1]
    have e2 := GlobalTheory.jTil_shift_block (D.nd.l i) _ D.R.t h w' η typ U hS a
      (AdmissibleParameterJ.JW D (decide (AdmissibleParameterJ.TypeU D ep (gA a))) (D.nd.j i) (ρA a)) (hU a) (b - w' a)
    rw [sub_add_cancel] at e2
    rw [← e2]
    exact if_congr (GlobalTheory.UseLoc.JumpBlock.jumps_iff D _ _ _ _) rfl rfl

end GlobalTheory.UseLocInst
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Pointwise

theorem thetaInner_swap {D : D7} {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (f g : WO S T' → ℂ) :
    thetaIP μ 𝓕 g f = star (thetaIP μ 𝓕 f g) := by
  unfold thetaIP
  rw [Complex.star_def, ← integral_conj]
  congr 1
  funext w
  rw [map_mul, Complex.conj_conj, ← Complex.star_def, mul_comm]

theorem rallisF_point : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), LevFix R i t → FactInf R i t → RealLow R i t → LevProd R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v, IsUnitVec R i v → ∀ (w : (R.cV i).W) (x y : (R.HW i (sg0 D A)).H), (∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) → ∀ γ ∈ GfC (Wc D i), ∀ h ∈ realLev R i, dimProd A i * rallisF R i t μ 𝓕 v (jointVec R i t v w) x y (γ * h) = thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) * coef R i t μ 𝓕 γ * trPair R i γ x y * (lowCoefSq R i v h : ℂ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hLF hFI hRL hLP μ 𝓕 hμ v hv w x y hS γ hγ h hh
  obtain ⟨u, hu, k, hk, rfl⟩ := hh
  have hkf : k ∈ GfC (Wc D i) := hLP.1 hk
  have hcomm : u * γ = γ * u := (GlobalTheory.AutMult.commute_inf_fin ⟨u, hu⟩ ⟨γ, hγ⟩).eq

  obtain ⟨Pc, hPc⟩ : ∃ Pc, (∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
      (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
        ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) = Pc := ⟨_, rfl⟩

  have hω : R.ωP i t (1, γ * (u * k)) (jointVec R i t v w) = R.ωP i t (1, u * γ) (jointVec R i t v w) := by
    have e : ((1 : GA D (Vc D i)), γ * (u * k)) = (1, u * γ) * (1, k) := by
      rw [Prod.mk_mul_mk, one_mul, hcomm, mul_assoc]
    rw [e, map_mul, Module.End.mul_apply]
    congr 1
    exact hLF k hk _

  have h1 : thetaIP μ 𝓕 (R.ωP i t (1, γ * (u * k)) (jointVec R i t v w)) (jointVec R i t v w) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) * star Pc * coef R i t μ 𝓕 γ := by
    rw [hω]
    have hF := hFI μ 𝓕 hμ u hu γ hγ (R.ioP i (PiTensorProduct.tprod ℂ v) w) (R.ioP i (PiTensorProduct.tprod ℂ v) w)
    have hR := hRL μ 𝓕 hμ v hv w u hu
    rw [hPc] at hR
    unfold jointVec at hR ⊢
    rw [hF, thetaInner_swap, hR, star_mul', ← thetaInner_swap]

  have hval : ∀ z, val R i v y (z * (γ * (u * k))) = val R i v y (z * (u * γ)) := by
    intro z
    have hmem : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := by
      rw [← (hL.models.HW i (sg0 D A)).2.1]
      exact LinearMap.mem_range_self _ y
    have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
    have hl := hm.lev (fun ρ => v ρ) k hk (z * (u * γ))
    unfold val
    rw [hLP.2.1 k hk, one_mul] at hl
    rw [← hl, hcomm]
    simp only [mul_assoc]
  have h2 := hS u hu γ hγ
  rw [hPc] at h2
  simp only [← hval] at h2

  have hinf : ∀ ρ, infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) (u * k) = infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u := by
    intro ρ
    rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul]
    have hk1 : infHom (Wc D i) k = 1 := hkf
    have e : infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) k = 1 := by
      show ((infHom (Wc D i) k).1).map (R.θ ρ) = 1
      rw [hk1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e, Matrix.mul_one]
  have h3 : ((lowCoefSq R i v (u * k) : ℝ) : ℂ) = star Pc * Pc := by
    unfold lowCoefSq
    simp only [hinf]
    rw [hPc]
    push_cast
    rw [Complex.star_def, Complex.conj_mul']
  unfold rallisF
  rw [h1, h3]
  linear_combination (thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) * star Pc * coef R i t μ 𝓕 γ) * h2

end GlobalTheory.RawLift.Pointwise

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU


theorem _root_.GlobalTheory.T.localLatticeIndex_cartanDecomposition_eq_normPow : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.LFun.IsFrameAt w (frameLat T) a → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ∀ g : GlobalTheory.FinZeta.Gv T v, GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g = a * (k₁ * t * k₂) * a⁻¹ → GlobalTheory.LocKerMod.idxAt T w h g = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := by
  first | exact @GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow | exact GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow | (intros; apply GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

theorem _root_.GlobalTheory.T.level_averages_theta_pair_zero_without_character : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), NoChi R i t y → ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ κ : G → GA D (Vc D i), GlobalTheory.DownLift.GenFinite.IsLifts R i t κ → ∀ f : WO (Vc D i) (Wc D i) → ℂ, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (GlobalTheory.DownLift.GenFinite.avgW R i t PP a tr ε κ f) l g = 0 := by
  first | exact @GlobalTheory.DownLift.GenFinite.avgLaw | exact GlobalTheory.DownLift.GenFinite.avgLaw | (intros; apply GlobalTheory.DownLift.GenFinite.avgLaw <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ F ∈ PPSet t K e, frob2 φ₂ F ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, frob2 φ₂ F = F ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  first | exact @GlobalTheory.CrysPrism.FrobPP.frob_mem_PPSet_congr | exact GlobalTheory.CrysPrism.FrobPP.frob_mem_PPSet_congr | (intros; apply GlobalTheory.CrysPrism.FrobPP.frob_mem_PPSet_congr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.frameReduction_eq_one_of_frameMatrix_congruent_one : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (k : GA D W) (PP : Pl D.host.E), finE W k ∈ St β → (∀ a b, Valued.v (GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b)) < 1) → redFn β PP (finE W k) = 1 := by
  first | exact @GlobalTheory.RedAt.redFn_finE_eq_one | exact GlobalTheory.RedAt.redFn_finE_eq_one | (intros; apply GlobalTheory.RedAt.redFn_finE_eq_one <;> assumption)
end

section


theorem _root_.GlobalTheory.T.generic_unitary_dual_gl : GlobalTheory.Published.UnitaryDualGL → GlobalTheory.Published.SquareIntegrableSegment → GlobalTheory.Published.GenericUnlinkedGL → GlobalTheory.Published.LanglandsMultisegments → GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.GenericUnitaryDualGL := by
  first | exact @GlobalTheory.GenericUnitaryBridge.genericUnitaryDualGL_of_hypotheses | exact GlobalTheory.GenericUnitaryBridge.genericUnitaryDualGL_of_hypotheses | (intros; apply GlobalTheory.GenericUnitaryBridge.genericUnitaryDualGL_of_hypotheses <;> assumption)
end
