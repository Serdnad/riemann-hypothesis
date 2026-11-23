module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle589
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle590
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle137
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle232
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle092
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle336
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Mathlib.Data.Multiset.Functor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqOfMemDpcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyZeroOfDeRhamCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle385
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle688
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle689
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.pow_smul_mem_lattice_of_acris_bound : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O), l ≠ 2 → ∀ ε : OCb l, IsEps ε → ∀ (j n c : ℕ), 2 * j < l - 1 → ∀ (u : TW (OB l O) T) (x : ↥T.L.T) (w : TW (OCr l O) T), (l : O) ^ n • u = (1 : OB l O) ⊗ₜ[O] x → toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ j) • ((l : O) ^ c • u) = TWincl (toOB l O) T w → ∃ x' : ↥T.L.T, (l : O) ^ c • u = (1 : OB l O) ⊗ₜ[O] x' := by
  first | exact @GlobalTheory.BKGal.Count.count | exact GlobalTheory.BKGal.Count.count | (intros; apply GlobalTheory.BKGal.Count.count <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isHausdorff_of_le_ideal {R : Type} [CommRing R] {I J : Ideal R} (h : I ≤ J) (hJ : IsHausdorff J R) :
    IsHausdorff I R := by
  refine ⟨fun x hx => hJ.haus x fun n => ?_⟩
  have h1 := hx n
  rw [SModEq.sub_mem] at h1 ⊢
  exact Submodule.smul_mono_left (Ideal.pow_right_mono h n) h1

theorem map_frobenius_charP {l : ℕ} [Fact l.Prime] {R O : Type} [CommRing R] [CharP R l] [CommRing O] [CharP O l]
    (ψ : R →+* O) (x : WittVector l R) :
    WittVector.map ψ (WittVector.frobenius x) = WittVector.frobenius (WittVector.map ψ x) := by
  ext n
  rw [WittVector.map_coeff, WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP,
    WittVector.map_coeff, map_pow]

theorem hom_comp_apply {l : ℕ} {R : Type} [CommRing R] {P P' P'' : Obj l R} (g : Hom P' P'') (f : Hom P P')
    (a : P.A) : (g.comp f).f a = g.f (f.f a) := rfl

theorem hom_eq_id_apply {l : ℕ} {R : Type} [CommRing R] {P P' : Obj l R} (g : Hom P' P) (f : Hom P P')
    (h : g.comp f = Hom.id P) (a : P.A) : g.f (f.f a) = a := by
  rw [← hom_comp_apply, h]; rfl

theorem hom_eq_comp_apply {l : ℕ} {R : Type} [CommRing R] {P P' P'' Q : Obj l R} (g : Hom P' P'') (f : Hom P P')
    (g' : Hom Q P'') (f' : Hom P Q) (h : g.comp f = g'.comp f') (a : P.A) : g.f (f.f a) = g'.f (f'.f a) := by
  rw [← hom_comp_apply, h]; rfl

theorem mapE_facts {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (O : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O) (hx0 : ψ bk.flat ≠ 0)
    (hxu : ¬ IsUnit (ψ bk.flat)) (hxc : IsAdicComplete (Ideal.span {ψ bk.flat}) O) :
    WittVector.map ψ (bk.ev bk.E) ∈ nonZeroDivisors (WittVector l O) ∧
    IsHausdorff ((Ideal.span {((l : ℕ) : WittVector l (OCb l))} ⊔ Ideal.span {bk.ev bk.E}).map (WittVector.map ψ))
      (WittVector l O) := by
  obtain ⟨w, -, hwE⟩ := GlobalTheory.T.breuilKisin_eisenstein_image_teichmuller_pow l K bk O ψ hxu
  have hE0 : WittVector.map ψ (bk.ev bk.E) ≠ 0 := fun h => by
    have h1 := congrArg (WittVector.constantCoeff (p := l) (R := O)) h
    rw [hwE, map_add (f := _), map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, map_zero] at h1
    exact hx0 ((pow_eq_zero_iff bk.deg_pos.ne').1 h1)
  refine ⟨mem_nonZeroDivisors_of_ne_zero hE0, isHausdorff_of_le_ideal ?_
    (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l O (ψ bk.flat) hx0 hxc).2.toIsHausdorff⟩
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]
  refine sup_le le_sup_left ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hwE]
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ bk.deg_pos))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem isHausdorff_map_congr {A B : Type} [CommRing A] [CommRing B] {I J : Ideal A} {g h : A →+* B} (hIJ : I = J)
    (hgh : g = h) (H : IsHausdorff (J.map h) B) : IsHausdorff (I.map g) B := by
  subst hIJ; subst hgh; exact H

theorem envPoint_eq {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X))
    (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O)
    (hx0 : ψ bk.flat ≠ 0) (hxu : ¬ IsUnit (ψ bk.flat)) (hxc : IsAdicComplete (Ideal.span {ψ bk.flat}) O)
    (F : En.Q.A →+* WittVector l O) (hFφ : ∀ a, F (En.Q.D.φ a) = WittVector.frobenius (F a))
    (hFinl : F.comp En.inl.f = WittVector.map ψ) (s : Hom En.Q (ainfObj K)) (hs1 : s.comp En.inl = Hom.id _)
    (hinr : F (BK.hf En.inr X) = WittVector.map ψ (s.f (BK.hf En.inr X))) (a : En.Q.A) :
    F a = WittVector.map ψ (s.f a) := by
  have hFi : ∀ b : WittVector l (OCb l), F (En.inl.f b) = WittVector.map ψ b := fun b => RingHom.congr_fun hFinl b
  have htfW : ∀ c : WittVector l O, ((l : ℕ) : WittVector l O) * c = 0 → c = 0 := fun c hc =>
    WittVector.eq_zero_of_p_mul_eq_zero c (by rw [mul_comm, hc])
  obtain ⟨F', hF'a⟩ : ∃ F' : En.Q.A →+* WittVector l O, ∀ a, F' a = WittVector.map ψ (s.f a) :=
    ⟨(WittVector.map ψ).comp s.f, fun _ => rfl⟩
  have hF'φ : ∀ a, F' (En.Q.D.φ a) = WittVector.frobenius (F' a) := fun a =>
    ((hF'a _).trans (congrArg (WittVector.map ψ) (Hom.f_φ s a))).trans
      ((map_frobenius_charP ψ (s.f a)).trans (congrArg WittVector.frobenius (hF'a a).symm))
  have hinl : ∀ b, F (En.inl.f b) = F' (En.inl.f b) := fun b =>
    (hFi b).trans ((congrArg (WittVector.map ψ) (hom_eq_id_apply s En.inl hs1 b).symm).trans (hF'a _).symm)
  have hE := (mapE_facts bk O ψ hx0 hxu hxc).1
  have hH := (mapE_facts bk O ψ hx0 hxu hxc).2
  have hnzd : F (En.inl.f (bk.ev bk.E)) ∈ nonZeroDivisors (WittVector l O) := by
    rw [hFi]; exact hE
  have hI : (ainfObj K).I = Ideal.span {bk.ev bk.E} := bk.span_ev.symm
  have hhaus : IsHausdorff ((Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I).map (F.comp En.inl.f))
      (WittVector l O) :=
    isHausdorff_map_congr (congrArg (Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ ·) hI) hFinl hH
  have hFF : F = F' :=
    GlobalTheory.T.breuilKisinPrismCoproduct_hom_eq_of_agree l K bk (ainfObj K) (bk.ev bk.E) (bk.ev X) En (WittVector l O) WittVector.frobenius F F'
      htfW hFφ hF'φ hinl (hinr.trans (hF'a _).symm) hnzd hhaus
  rw [hFF, hF'a]

theorem envPoint_factors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharP O l] [PerfectRing O l] (f : En.Q.A →+* O), f (En.inl.f (bk.ev X)) ≠ 0 →
    ¬ IsUnit (f (En.inl.f (bk.ev X))) → IsAdicComplete (Ideal.span {f (En.inl.f (bk.ev X))}) O →
    ∃ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)) (ψ : OCb l →+* O), s.comp En.inl = Hom.id _ ∧
      s.comp En.inr = (ainfHom K g).comp bk.ι ∧
      ∀ a, f a = ψ (WittVector.coeff (p := l) (R := OCb l) (s.f a) 0) := by
  intro l _ K bk En O _ _ _ _ _ f hx0 hxu hxc
  have hcc : Function.Surjective (WittVector.constantCoeff (p := l) (R := OCb l)) := fun y =>
    ⟨WittVector.teichmuller l y, by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩
  let f0 : WittVector l (OCb l) →+* O := f.comp En.inl.f
  have hker : RingHom.ker (WittVector.constantCoeff (p := l) (R := OCb l)) ≤ RingHom.ker f0 := by
    rw [WittVector.ker_constantCoeff, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      map_natCast, CharP.cast_eq_zero]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : OCb l →+* O, ∀ a : WittVector l (OCb l), f (En.inl.f a) = ψ (a.coeff 0) :=
    ⟨RingHom.liftOfSurjective _ hcc ⟨f0, hker⟩, fun a =>
      (RingHom.liftOfSurjective_comp_apply _ hcc ⟨f0, hker⟩ a).symm⟩
  have hflat : f (En.inl.f (bk.ev X)) = ψ bk.flat := by
    rw [hψ, bk.ev_X, WittVector.teichmuller_coeff_zero]
  rw [hflat] at hx0 hxu hxc
  obtain ⟨htf, -, -⟩ := GlobalTheory.T.ainf_envelope_mod_prime_properties l K bk En
  obtain ⟨F, hF0, hFφ⟩ := GlobalTheory.T.exists_frobenius_compatible_wittVector_lift l En.Q.A En.Q.D.φ
    (fun a => ⟨En.Q.D.δ a, by rw [En.Q.D.φ_eq]; ring⟩) htf O f
  have hFinl : F.comp En.inl.f = WittVector.map ψ :=
    GlobalTheory.T.wittVector_ringHom_eq_map_of_coeff_zero l (OCb l) O (F.comp En.inl.f) ψ (fun a => (hF0 (En.inl.f a)).trans (hψ a))
  have hFi : ∀ b : WittVector l (OCb l), F (En.inl.f b) = WittVector.map ψ b := fun b => RingHom.congr_fun hFinl b

  have hφX : En.Q.D.φ (BK.hf En.inr X) = BK.hf En.inr X ^ l :=
    calc En.Q.D.φ (BK.hf En.inr X) = BK.hf En.inr (frobS l bk.a X) := (Hom.f_φ En.inr X).symm
      _ = BK.hf En.inr (X ^ l) := by rw [frobS_X]
      _ = _ := map_pow _ _ _
  set v := F (BK.hf En.inr X) with hvdef
  have hv : WittVector.frobenius v = v ^ l := by
    rw [hvdef, ← hFφ, hφX, map_pow]
  have hvt := GlobalTheory.T.wittVector_eq_teichmuller_of_frobenius_eq_pow_self l O v hv
  have e1 : F (En.inl.f (bk.ev X)) = WittVector.teichmuller l (ψ bk.flat) := by
    rw [hFi, bk.ev_X, WittVector.map_teichmuller]
  have e2 : F (En.inl.f (bk.ev bk.E)) = WittVector.map ψ (bk.ev bk.E) := hFi _
  have h1 : v = F (En.inl.f (bk.ev X)) + F (En.inl.f (bk.ev bk.E)) * F En.w := by
    have := congrArg F En.w_eq
    rwa [map_add, map_mul] at this
  rw [e1, e2] at h1
  have hdvd : WittVector.map ψ (bk.ev bk.E) ∣
      WittVector.teichmuller l (v.coeff 0) - WittVector.teichmuller l (ψ bk.flat) :=
    ⟨F En.w, by rw [← hvt]; linear_combination h1⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_conj_of_teichmuller_congr l K bk O ψ hx0 hxu hxc (v.coeff 0) hdvd
  obtain ⟨s, ⟨hs1, hs2⟩, -⟩ := En.univ (ainfObj K) (Hom.id _) ((ainfHom K g).comp bk.ι)

  have hinr : F (BK.hf En.inr X) = WittVector.map ψ (s.f (BK.hf En.inr X)) := by
    have h2 : s.f (BK.hf En.inr X) = Per.σA (g : GQ l) (bk.ev X) :=
      hom_eq_comp_apply s En.inr _ _ hs2 X
    have h3 : WittVector.map ψ (Per.σA (g : GQ l) (bk.ev X)) =
        WittVector.teichmuller l (ψ (Per.σF (g : GQ l) bk.flat)) := by
      rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich, WittVector.map_teichmuller]
    refine Eq.trans ?_ ((congrArg (WittVector.map ψ) h2).trans h3).symm
    exact hvdef.symm.trans (hvt.trans (congrArg (WittVector.teichmuller l) hg))
  refine ⟨g, s, ψ, hs1, hs2, fun a => ?_⟩
  rw [← hF0, envPoint_eq bk En O ψ hx0 hxu hxc F hFφ hFinl s hs1 hinr a]
  exact WittVector.map_coeff ψ (s.f a) 0

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.TwoCopy

variable {l : ℕ} [hl : Fact l.Prime]

theorem dvd_pow_of_ne_zero {π b : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l)) (hb : b ≠ 0) :
    ∃ n : ℕ, b ∣ π ^ n := by
  haveI := GlobalTheory.FrobInt.valuationRing_tilt l
  by_contra h
  push_neg at h
  apply hb
  refine hπ.haus b fun n => ?_
  obtain ⟨c, hc⟩ : π ^ n ∣ b := by
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond b (π ^ n)
    · exact absurd ⟨c, hc.symm⟩ (h n)
    · exact ⟨c, hc.symm⟩
  rw [SModEq.zero, hc, ← smul_eq_mul]
  exact Submodule.smul_mem_smul (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
    Submodule.mem_top

theorem isUnit_of_ne_zero {T : Type} [CommRing T] {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l))
    (i : OCb l →+* T) (hu : IsUnit (i π)) (y : OCb l) (hy : y ≠ 0) : IsUnit (i y) := by
  obtain ⟨n, c, hc⟩ := dvd_pow_of_ne_zero hπ hy
  exact isUnit_of_mul_isUnit_left (y := i c) (by rw [← map_mul, ← hc, map_pow]; exact hu.pow n)

theorem exists_ext {T : Type} [CommRing T] {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l))
    (i : OCb l →+* T) (hu : IsUnit (i π)) :
    ∃ j : Cb l →+* T, ∀ y, j (algebraMap (OCb l) (Cb l) y) = i y :=
  ⟨IsLocalization.lift (M := nonZeroDivisors (OCb l)) (S := Cb l) (g := i)
      fun y => isUnit_of_ne_zero hπ i hu y (nonZeroDivisors.ne_zero y.2),
    fun y => IsLocalization.lift_eq _ y⟩

theorem exists_clear {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l)) (x : Cb l) :
    ∃ (n : ℕ) (y : OCb l), algebraMap (OCb l) (Cb l) π ^ n * x = algebraMap (OCb l) (Cb l) y := by
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (OCb l)) x
  obtain ⟨n, c, hc⟩ := dvd_pow_of_ne_zero hπ (nonZeroDivisors.ne_zero b.2)
  refine ⟨n, c * a, ?_⟩
  simp only at h
  rw [← map_pow, hc, map_mul, map_mul, ← h]
  ring

theorem exists_clear_family {κ : Type} [Fintype κ] {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l))
    (x : κ → Cb l) : ∃ (m : ℕ) (x' : κ → OCb l), ∀ j,
      algebraMap (OCb l) (Cb l) π ^ m * x j = algebraMap (OCb l) (Cb l) (x' j) := by
  choose n y hy using fun j => exists_clear hπ (x j)
  refine ⟨∑ j, n j, fun j => π ^ (∑ i, n i - n j) * y j, fun j => ?_⟩
  have hle : n j ≤ ∑ i, n i := Finset.single_le_sum (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ j)
  rw [map_mul, ← hy j, map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem map_constantCoeff_surj {F : Type} [CommRing F] (a : F⟦X⟧) :
    ∃ s : (WittVector l F)⟦X⟧, PowerSeries.map (WittVector.constantCoeff (p := l) (R := F)) s = a :=
  ⟨PowerSeries.mk fun n => WittVector.teichmuller l (PowerSeries.coeff n a), by
    ext n
    simp [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

end GlobalTheory.BSP.TwoCopy

namespace GlobalTheory.BSP.TwoCopy

theorem mem_reduction_of_invariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ]
    (x : κ → Cb l), (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, autCb l (galTilt l (g : GQ l)) (x j) = x j) →
    (∀ (T : Type) [CommRing T] (i₁ i₂ : Cb l →+* T),
      (∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), i₁ y = i₂ y) →
      ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) →
    ∀ j, x j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  intro l _ K bk κ _ x hfix hφ
  obtain ⟨ek, prA, hek, hinj, hpr, hpr1⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  obtain ⟨hoe, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨-, -, -, h0, -, hc, -⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  have hH : IsHausdorff (Ideal.span {bk.flat}) (OCb l) := hc.toIsHausdorff
  have hX : ek X = bk.flat := by
    have := hek X
    rwa [PowerSeries.map_X, bk.ev_X, WittVector.teichmuller_coeff_zero] at this
  obtain ⟨m, x', hx'⟩ := exists_clear_family hH x
  letI : Algebra (Fq l bk.a)⟦X⟧ (OCb l) := ek.toAlgebra
  have halg : ∀ a, algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a = ek a := fun _ => rfl
  haveI : Module.IsTorsionFree (Fq l bk.a)⟦X⟧ (OCb l) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hinj
  let pr : OCb l →ₗ[(Fq l bk.a)⟦X⟧] (Fq l bk.a)⟦X⟧ :=
    { toFun := prA
      map_add' := prA.map_add
      map_smul' := fun a y => by rw [Algebra.smul_def, halg, hpr, RingHom.id_apply, smul_eq_mul] }
  have hEq : ∀ (T : Type) [CommRing T] (i₁ i₂ : OCb l →+* T),
      (∀ a, i₁ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a) = i₂ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a)) →
      IsUnit (i₁ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)) →
      ∃ c : κ → κ → T, ∀ j, i₁ (x' j) - i₂ (x' j) = ∑ i, (i₁ (x' i) - i₂ (x' i)) ^ l * c i j := by
    intro T _ i₁ i₂ hag hu
    have hag' : ∀ a, i₁ (ek a) = i₂ (ek a) := hag
    rw [halg, hX] at hu
    have hf : i₁ bk.flat = i₂ bk.flat := by rw [← hX]; exact hag' X
    obtain ⟨j₁, hj₁⟩ := exists_ext hH i₁ hu
    obtain ⟨j₂, hj₂⟩ := exists_ext hH i₂ (hf ▸ hu)
    have hOE : ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), j₁ y = j₂ y := by
      intro y hy
      obtain ⟨n, s, hs⟩ := (hoe y).1 hy
      have hs' : i₁ ((bk.ev s).coeff 0) = i₂ ((bk.ev s).coeff 0) := by rw [← hek s]; exact hag' _
      have e1 := congrArg j₁ hs
      have e2 := congrArg j₂ hs
      rw [map_mul, map_pow, hj₁, hj₁, hs'] at e1
      rw [map_mul, map_pow, hj₂, hj₂, ← hf] at e2
      exact (hu.pow n).mul_left_cancel (e1.trans e2.symm)
    obtain ⟨c, hc'⟩ := hφ T j₁ j₂ hOE
    obtain ⟨υ, hυ⟩ := hu
    refine ⟨fun i j => c i j * (υ : T) ^ m * ((υ⁻¹ : Tˣ) : T) ^ (m * l), fun j => ?_⟩
    have hx1 : ∀ i, i₁ (x' i) = (υ : T) ^ m * j₁ (x i) := fun i => by
      rw [← hj₁, ← hx' i, map_mul, map_pow, hj₁, ← hυ]
    have hx2 : ∀ i, i₂ (x' i) = (υ : T) ^ m * j₂ (x i) := fun i => by
      rw [← hj₂, ← hx' i, map_mul, map_pow, hj₂, ← hf, ← hυ]
    have hinv : (υ : T) ^ (m * l) * ((υ⁻¹ : Tˣ) : T) ^ (m * l) = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    simp only [hx1, hx2]
    rw [← mul_sub, hc' j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, mul_pow, ← pow_mul]
    linear_combination (-((υ : T) ^ m * (j₁ (x i) - j₂ (x i)) ^ l * c i j)) * hinv
  have hPts : ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (ψ ψ' : OCb l →+* O), ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X) ≠ 0 →
      ¬ IsUnit (ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)) →
      IsAdicComplete (Ideal.span {ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)}) O →
      (∀ a, ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a) = ψ' (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a)) →
      ∀ j, ψ (x' j) = ψ' (x' j) := by
    intro O _ _ _ _ _ ψ ψ' h1 h2 h3 hag j
    rw [halg, hX] at h1 h2 h3
    have hag' : ∀ a, ψ (ek a) = ψ' (ek a) := hag
    obtain ⟨g, hg, hψ⟩ := GlobalTheory.T.exists_fixFlat_of_tilt_maps_agree l K bk O ψ h1 h2 h3 ψ' (fun s => by rw [← hek s]; exact hag' _)
    have hg' : Per.σF (g : GQ l) bk.flat = bk.flat := hg
    rw [hψ]
    congr 1
    apply IsFractionRing.injective (OCb l) (Cb l)
    rw [← galTilt_apply, ← autCb_alg, ← hx' j, map_mul, map_pow, autCb_alg, hfix g hg j, galTilt_apply, hg']
  have hnz : algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X ∈ nonZeroDivisors (OCb l) := by
    rw [halg, hX]; exact mem_nonZeroDivisors_of_ne_zero h0
  have hHX : IsHausdorff (Ideal.span {algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X}) (OCb l) := by
    rw [halg, hX]; exact hH
  have key := GlobalTheory.T.descent_of_points_killed_alt l (Fq l bk.a)⟦X⟧ (OCb l) X pr (CharP.cast_eq_zero _ _) hnz hHX κ x' hEq hPts hpr1
  intro j
  obtain ⟨s, hs⟩ := map_constantCoeff_surj (l := l) (prA (x' j))
  refine (hoe (x j)).2 ⟨m, s, ?_⟩
  rw [hx' j, ← hek s, hs]
  exact congrArg _ (key j)

end GlobalTheory.BSP.TwoCopy
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.norm_eisenstein_mul_closedDisc_eq_rpow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ y : bk.DS ρ, ‖toDisc l (X : bk.S) ρ bk.E * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖ := by
  first | exact @GlobalTheory.BSP.BK.norm_toDisc_E_mul | exact GlobalTheory.BSP.BK.norm_toDisc_E_mul | (intros; apply GlobalTheory.BSP.BK.norm_toDisc_E_mul <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.satakeParameter_spherical_product_spehQuotients : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (c n : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (ρ : ∀ i, LocIrr w (a i)) (σ : ∀ i, LocIrr w (d i * a i)), (∀ i, 1 ≤ d i) → (∀ i, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i).ρ (ρ i).smooth (ρ i).irred) (d i) (σ i).ρ) → ∀ T : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w (locProd h w σ) T → ∃ S : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) ∧ ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) = T.map (fun z => (z : ℂ)) := by
  first | exact @GlobalTheory.SatInd.satake_locProd_speh | exact GlobalTheory.SatInd.satake_locProd_speh | (intros; apply GlobalTheory.SatInd.satake_locProd_speh <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

namespace GlobalTheory.PotDirect

theorem main : StepPotDirect := by
  intro D P hT hFo h0 hBr hPH hChi hIE h12 hTen hTP i k hl r ρ hr π hπ hdec Xs hπX hTL w hw
  obtain ⟨Y, u, hu, hY, hYc, hX, hχ, hχσ⟩ := GlobalTheory.TypeInertia.inertial_chars D P hT h0 hPH hChi i k hl r hr Xs hTL w hw
  have hχc : Continuous fun g => ((chiGL i g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have hab : a = b := Subsingleton.elim a b
    subst hab
    simpa [chiGL, Matrix.scalar] using D.nd.chi_cont i 1
  obtain ⟨K', h, hN, hF', hS, hpc, hpc0, hker⟩ := GlobalTheory.PotExt.main D P h12 i k w hw Y (fun y hy => (hY y hy).1) (↥Xs) D.R.nV
    (fun x => r x) 1 (chiGL i) (fun x => (hr x).1) hχc (fun x => (hX x x.2).1) hχ
  obtain ⟨ch, hch⟩ := GlobalTheory.InertiaChars.main D P hTP hIE i k hl w hw Y hY K' h hN hF' hS hker
  have hdeg := (GlobalTheory.TypeDegOne.degree_one D i k hl).2 w hw
  refine GlobalTheory.T.twistedFamily_potentiallyCrystalline_frobStable D hTen i w hw hdeg r Xs K' h hN hF' hS (Y.image ch) (ch u) (D.R.nV + 1)
    (Finset.mem_image_of_mem _ hu) (Finset.card_image_le.trans hYc) (fun x _ => (hr x).1) ?_ hpc0 ?_
  · intro x hx
    obtain ⟨M, hM, hσ⟩ := (hX x hx).2
    exact ⟨hpc ⟨x, hx⟩, hch Y subset_rfl _ (r x) (hr x).1 (hpc ⟨x, hx⟩) M hM hσ⟩
  · have := hch {u} (by simpa using hu) 1 (chiGL i) hχc hpc0 {u} (by simp) (fun σ hσ => by simpa using hχσ σ hσ)
    simpa using this

end GlobalTheory.PotDirect
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

theorem _root_.GlobalTheory.T.integrableOn_downwardThetaLift_integrand : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := by
  first | exact @GlobalTheory.DownLift.GenFinite.integrableOn_downIntegrand | exact GlobalTheory.DownLift.GenFinite.integrableOn_downIntegrand | (intros; apply GlobalTheory.DownLift.GenFinite.integrableOn_downIntegrand <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.exists_heckeL_eq_toricSum_ne_zero : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : Formalism.L2.Host.HChar H.E), IsHostDatum H φ s κ 𝔣 χ → ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ s ≠ 0 ∧ ∀ T : ℂ, IsToricSum φ s κ 𝔣 χ T ↔ T = Λ s := by
  first | exact @GlobalTheory.ToricValue.exists_heckeL_toricSum | exact GlobalTheory.ToricValue.exists_heckeL_toricSum | (intros; apply GlobalTheory.ToricValue.exists_heckeL_toricSum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.goodProjector_conv_mirabolicAvg_eq_zero : GlobalTheory.MirAvg.SeriesKillsAvg → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), GlobalTheory.LiftRows.Given R F → ∀ (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 →
    ∀ (b : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ x : G,
      ∑ y : G, GlobalTheory.DownLift.mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x) = 0 := by
  first | exact @GlobalTheory.GoodNoChiTr.conv_mirC_eC | exact GlobalTheory.GoodNoChiTr.conv_mirC_eC | (intros; apply GlobalTheory.GoodNoChiTr.conv_mirC_eC <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

theorem _root_.GlobalTheory.T.thetaFunction_levelType_mem_span_averages : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeVec R i t f → f ∈ Submodule.span ℂ ({φ | GlobalTheory.DownLift.GenFinite.TypeVec R i t φ ∧ GlobalTheory.DownLift.GenFinite.Clean R i t φ} ∪ GlobalTheory.DownLift.GenFinite.AvgIm R i t) := by
  first | exact @GlobalTheory.DownLift.GenFinite.cleanSpan | exact GlobalTheory.DownLift.GenFinite.cleanSpan | (intros; apply GlobalTheory.DownLift.GenFinite.cleanSpan <;> assumption)
end
