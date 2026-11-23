module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TwFil

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem dpw_mul {R : Type} [CommRing R] (k : ℕ) (c x : WittVector l R) :
    dpw k (c * x) = algebraMap _ (WL l R) c ^ k * dpw k x := by
  simp only [dpw, map_mul, mul_pow]; ring

theorem exists_gal_xi (σ : Gal(PadicAlgCl l/K)) : ∃ c : Ainf l, σ • xi0 l = c * xi0 l := by
  have h : σ • xi0 l ∈ RingHom.ker (theta0 l) := ACris.gal_smul_mem_ker σ xi0_mem
  rw [ker_theta0] at h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨c, hc.symm⟩

theorem exists_twId_xi (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) :
    ∃ c : A.W, WittVector.map (twId σ A) (tw σ A).xi = c * A.xi := by
  obtain ⟨c, hc⟩ := exists_gal_xi σ
  refine ⟨A.sW c, ?_⟩
  have e : WittVector.map (twId σ A) (tw σ A).xi = A.sW (WittVector.map (galOb σ) (xi0 l)) := by
    rw [xi, sW, sW, ← wmap_comp, galois_twist_identity_section, wmap_comp]
  have hc' : WittVector.map (galOb σ) (xi0 l) = c * xi0 l := hc
  rw [e, hc', map_mul]; rfl

def twBack (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : A.A →+* (tw σ A).A := RingHom.id A.A

theorem exists_twBack_xi (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) :
    ∃ c : (tw σ A).W, WittVector.map (twBack σ A) A.xi = c * (tw σ A).xi := by
  obtain ⟨c, hc⟩ := exists_gal_xi σ⁻¹
  refine ⟨(tw σ A).sW c, ?_⟩
  have e : WittVector.map (twBack σ A) A.xi = (tw σ A).sW (σ⁻¹ • xi0 l) := by
    have h : WittVector.map (galOb σ) (σ⁻¹ • xi0 l) = xi0 l := smul_inv_smul σ (xi0 l)
    have e2 : (A.xi : WittVector l A.A) = (tw σ A).sW (σ⁻¹ • xi0 l) :=
      (congrArg (WittVector.map A.s) h.symm).trans (wmap_comp _ _ _).symm
    exact (wmap_id A.xi).trans e2
  rw [e, hc, map_mul]; rfl

theorem pdOk_twBack (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : PdOk (twBack σ A) := fun k => by
  obtain ⟨c, hc⟩ := exists_twBack_xi σ A
  rw [hc, dpw_mul]
  exact mul_mem (pow_mem (Subalgebra.algebraMap_mem _ c) k) ((tw σ A).dpw_xi_mem k)

theorem acrisZero_map_dividedXi {A B : PAlg l} {f : A.A →+* B.A} (h : PdOk f) {c : B.W}
    (hc : WittVector.map f A.xi = c * B.xi) (k : ℕ) :
    h.acr0 (A.dxi0 k) = algebraMap B.W B.Acr0 c ^ k * B.dxi0 k :=
  Subtype.ext (by
    have := awayW_dpw f k (A.isUnit_natCast k.factorial_ne_zero) A.xi
    rw [hc, dpw_mul] at this
    exact this)

theorem acrisZero_map_preserves_filtration {A B : PAlg l} {f : A.A →+* B.A} (h : PdOk f) {c : B.W}
    (hc : WittVector.map f A.xi = c * B.xi) (r : ℕ) : ∀ x ∈ A.Fil0 r, h.acr0 x ∈ B.Fil0 r := by
  have h' : A.Fil0 r ≤ (B.Fil0 r).comap h.acr0 := by
    rw [Fil0, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, acrisZero_map_dividedXi h hc]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, hk, rfl⟩)
  exact fun x hx => h' hx

theorem acr_fil_of {A B : PAlg l} {f : A.A →+* B.A} (h : PdOk f) {c : B.W}
    (hc : WittVector.map f A.xi = c * B.xi) (n r : ℕ) : ∀ x ∈ A.Fil n r, h.acr n x ∈ B.Fil n r := by
  have h' : A.Fil n r ≤ (B.Fil n r).comap (h.acr n) := by
    rw [Fil, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    change h.acr n (A.mkAcr n (A.dxi0 k)) ∈ _
    rw [PdOk.acr_mk, acrisZero_map_dividedXi h hc, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, hk, rfl⟩)
  exact fun x hx => h' hx

theorem twist_acrisZero_preserves_filtration (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (r : ℕ) :
    ∀ x ∈ (tw σ A).Fil0 r, (pdOk_twId σ A).acr0 x ∈ A.Fil0 r := by
  obtain ⟨c, hc⟩ := exists_twId_xi σ A
  exact acrisZero_map_preserves_filtration (pdOk_twId σ A) hc r

theorem twAcr_fil (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n r : ℕ) :
    ∀ x ∈ (tw σ A).Fil n r, twAcr σ A n x ∈ A.Fil n r := by
  obtain ⟨c, hc⟩ := exists_twId_xi σ A
  exact acr_fil_of (pdOk_twId σ A) hc n r

theorem acr_eq_self {A : PAlg l} {f : A.A →+* A.A} (h : PdOk f) (hf : f = RingHom.id _) (n : ℕ) (x : A.Acr n) :
    h.acr n x = x := by
  subst hf; exact PdOk.acr_id h n x

theorem pdOk_self (A : PAlg l) : PdOk (RingHom.id A.A) := fun k => by
  rw [wmap_id]; exact A.dpw_xi_mem k

theorem twAcr_bijective (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) : Function.Bijective (twAcr σ A n) := by
  have e1 : (twBack σ A).comp (twId σ A) = RingHom.id (tw σ A).A := RingHom.ext fun _ => rfl
  have e2 : (twId σ A).comp (twBack σ A) = RingHom.id A.A := RingHom.ext fun _ => rfl
  have h1 : PdOk ((twBack σ A).comp (twId σ A)) := e1 ▸ pdOk_self (tw σ A)
  have h2 : PdOk ((twId σ A).comp (twBack σ A)) := e2 ▸ pdOk_self A
  refine Function.bijective_iff_has_inverse.2 ⟨(pdOk_twBack σ A).acr n, fun x => ?_, fun x => ?_⟩
  · exact (PdOk.acr_comp (pdOk_twId σ A) (pdOk_twBack σ A) h1 n x).symm.trans (acr_eq_self h1 e1 n x)
  · exact (PdOk.acr_comp (pdOk_twBack σ A) (pdOk_twId σ A) h2 n x).symm.trans (acr_eq_self h2 e2 n x)

theorem twAcr_phi (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (x : (tw σ A).Acr n) :
    twAcr σ A n ((tw σ A).phi n x) = A.phi n (twAcr σ A n x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine congrArg (A.mkAcr n) (Subtype.ext ?_)
  change awayW (twId σ A) (awayW (tw σ A).frob y.1) = awayW A.frob (awayW (twId σ A) y.1)
  rw [← RingHom.comp_apply, ← awayW_comp, ← RingHom.comp_apply, ← awayW_comp]
  rfl

theorem exists_phiW (A : PAlg l) (x : A.W) : ∃ y : A.W, A.phiW x = x ^ l + (l : A.W) * y := by
  have h : A.phiW x - x ^ l ∈ Ideal.span {(l : A.W)} := by
    rw [mem_span_l_iff, ← WittVector.constantCoeff_apply, map_sub, map_pow, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, phiW, WittVector.map_coeff, sub_eq_zero]
    rfl
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨y, by rw [mul_comm, hy]; ring⟩

theorem factorial_mul_divided_power_xi (A : PAlg l) (k : ℕ) :
    (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k := Subtype.ext (by
  change (k.factorial : WL l A.A) * dpw k A.xi = algebraMap _ (WL l A.A) A.xi ^ k
  rw [dpw, ← mul_assoc, Ring.mul_inverse_cancel _ (A.isUnit_natCast k.factorial_ne_zero), one_mul])

theorem natCast_cancel (A : PAlg l) {k : ℕ} (hk : k ≠ 0) {a b : A.Acr0}
    (h : (k : A.Acr0) * a = (k : A.Acr0) * b) : a = b :=
  Subtype.ext ((A.isUnit_natCast hk).mul_left_cancel (congrArg Subtype.val h))

theorem acrisZero_map_algebraMap {A B : PAlg l} {f : A.A →+* B.A} (h : PdOk f) (x : A.W) :
    h.acr0 (algebraMap A.W A.Acr0 x) = algebraMap B.W B.Acr0 (WittVector.map f x) :=
  Subtype.ext (awayW_algebraMap f x)

theorem exists_phi_xi (A : PAlg l) :
    ∃ v : A.Acr0, A.pdOk_frob.acr0 (algebraMap A.W A.Acr0 A.xi) = (l : A.Acr0) * v := by
  obtain ⟨y, hy⟩ := exists_phiW A A.xi
  refine ⟨((l - 1).factorial : A.Acr0) * A.dxi0 l + algebraMap A.W A.Acr0 y, ?_⟩
  rw [acrisZero_map_algebraMap]
  change algebraMap A.W A.Acr0 (A.phiW A.xi) = _
  rw [hy, map_add (f := _), map_pow, ← factorial_mul_divided_power_xi, map_mul, map_natCast, mul_add, ← mul_assoc, ← Nat.cast_mul,
    Nat.mul_factorial_pred (Fact.out : l.Prime).ne_zero]

theorem factorization_factorial_le (k : ℕ) (hk : 1 ≤ k) : (k.factorial).factorization l ≤ k - 1 := by
  have hp : l.Prime := Fact.out
  rw [Nat.factorization_def _ hp]
  have h : (l - 1) * multiplicity l k.factorial < k := sub_one_mul_multiplicity_factorial_lt_of_ne_zero l (n := k) (by omega)
  have h1 : 1 ≤ l - 1 := Nat.le_sub_of_add_le hp.two_le
  have h2 : multiplicity l k.factorial ≤ (l - 1) * multiplicity l k.factorial := Nat.le_mul_of_pos_left _ h1
  omega

theorem exists_factorial_mul (A : PAlg l) (k : ℕ) (hk : 1 ≤ k) :
    ∃ w : A.W, (k.factorial : A.W) * w = (l : A.W) ^ (k - 1) := by
  obtain ⟨c, hc⟩ := ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l) (Nat.factorial_ne_zero k)
    (factorization_factorial_le k hk)
  refine ⟨A.sW c, ?_⟩
  rw [← map_natCast A.sW, ← map_mul, hc, map_pow, map_natCast]

theorem frobenius_dividedXi_mem_span_prime (A : PAlg l) (k : ℕ) (hk : 1 ≤ k) :
    A.pdOk_frob.acr0 (A.dxi0 k) ∈ Ideal.span {(l : A.Acr0)} := by
  obtain ⟨v, hv⟩ := exists_phi_xi A
  obtain ⟨w, hw⟩ := exists_factorial_mul A k hk
  refine Ideal.mem_span_singleton'.2 ⟨algebraMap A.W A.Acr0 w * v ^ k, ?_⟩
  apply natCast_cancel A k.factorial_ne_zero
  have h1 : (k.factorial : A.Acr0) * A.pdOk_frob.acr0 (A.dxi0 k) = ((l : A.Acr0) * v) ^ k := by
    rw [← hv, ← map_pow, ← factorial_mul_divided_power_xi, map_mul, map_natCast]
  have h2 : (k.factorial : A.Acr0) * algebraMap A.W A.Acr0 w = (l : A.Acr0) ^ (k - 1) := by
    rw [← map_natCast (algebraMap A.W A.Acr0), ← map_mul, hw, map_pow, map_natCast]
  rw [h1]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h2
  linear_combination (v ^ (m + 1) * (l : A.Acr0)) * h2

theorem frob_pfil0 (A : PAlg l) : ∀ x ∈ A.PFil0, A.pdOk_frob.acr0 x ∈ Ideal.span {(l : A.Acr0)} := by
  have h : A.PFil0 ≤ (Ideal.span {(l : A.Acr0)}).comap A.pdOk_frob.acr0 := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_span_singleton_self _
    · rw [Fil0, Ideal.span_le]
      rintro _ ⟨k, hk, rfl⟩
      exact frobenius_dividedXi_mem_span_prime A k hk
  exact fun x hx => h hx

theorem tw_fil : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : Gal(PadicAlgCl l/K)), (∀ x ∈ (tw σ A).Fil0 1, (pdOk_twId σ A).acr0 x ∈ A.Fil0 1) ∧
    (∀ x ∈ A.PFil0, A.pdOk_frob.acr0 x ∈ Ideal.span {(l : A.Acr0)}) ∧
    (∀ n r, ∀ x ∈ (tw σ A).Fil n r, twAcr σ A n x ∈ A.Fil n r) ∧
    (∀ n, Function.Bijective (twAcr σ A n)) ∧
    ∀ n x, twAcr σ A n ((tw σ A).phi n x) = A.phi n (twAcr σ A n x) :=
  fun A _ σ => ⟨twist_acrisZero_preserves_filtration σ A 1, frob_pfil0 A, twAcr_fil σ A, twAcr_bijective σ A, twAcr_phi σ A⟩

end GlobalTheory.CompanionTheory.TwFil
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem resU_self_pullC : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) (x : CH.Cn (U.ι ⋙ F) n), (resU F k).pullC n x = x := by
  intro R _ C _ F U k n x
  funext s
  rfl

end GlobalTheory.CompanionTheory.KunGlue
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TiltFacts

variable (l : ℕ) [Fact l.Prime]

theorem isDomain_ob : IsDomain (CrystallineSemistableComparison.Ob l) :=
  IsPerfectoidField.isDomain_preTilt (K := ℂ_[l]) l

theorem norm_pFlat_eq : ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ = ‖(l : ℂ_[l])‖ := by
  rw [preTilt_norm_def, coe_untilt_pFlat]

theorem norm_pFlat_pos : 0 < ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ := by
  rw [norm_pFlat_eq]
  exact norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem norm_pFlat_lt_one : ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ < 1 := by
  rw [norm_pFlat_eq]
  exact IsPerfectoidField.norm_natCast_lt_one

theorem rt_pow (k : ℕ) : CrystallineSemistableComparison.D.rt l k ^ l ^ k = pFlat l := by
  have h := (iterateFrobeniusEquiv (CrystallineSemistableComparison.Ob l) l k).apply_symm_apply (pFlat l)
  rwa [iterateFrobeniusEquiv_def] at h

theorem exists_dvd_pFlat_pow (a : CrystallineSemistableComparison.Ob l) (ha : a ≠ 0) : ∃ M : ℕ, a ∣ pFlat l ^ M := by
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 ha) (norm_pFlat_lt_one l)
  refine ⟨M, preTilt_dvd_iff_norm_le.2 ?_⟩
  rw [norm_pow]
  exact hM.le

theorem exists_rt_dvd (a : CrystallineSemistableComparison.Ob l) (ha : ¬ IsUnit a) : ∃ k : ℕ, CrystallineSemistableComparison.D.rt l k ∣ a := by
  have hlt : ‖a‖ < 1 := by
    refine lt_of_le_of_ne (preTilt_norm_le_one a) fun h => ha ?_
    exact (IsPerfectoidField.isUnit_iff_norm_untilt l).2 (by rwa [preTilt_norm_def] at h)
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pFlat_pos l) hlt
  have hnl : n ≤ l ^ n := (Nat.lt_pow_self hl).le
  refine ⟨n, preTilt_dvd_iff_norm_le.2 ?_⟩
  have h1 : ‖a‖ ^ l ^ n ≤ ‖CrystallineSemistableComparison.D.rt l n‖ ^ l ^ n := by
    rw [← norm_pow (CrystallineSemistableComparison.D.rt l n), rt_pow]
    exact (pow_le_pow_of_le_one (norm_nonneg _) hlt.le hnl).trans hn.le
  exact le_of_pow_le_pow_left₀ (pow_ne_zero _ (by omega)) (norm_nonneg _) h1

theorem obFacts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := by
  intro l _
  haveI := isDomain_ob l
  refine ⟨inferInstance, ?_, exists_dvd_pFlat_pow l, exists_rt_dvd l⟩
  refine (ValuationRing.iff_dvd_total).2 ⟨fun a b => ?_⟩
  rcases le_total ‖a‖ ‖b‖ with h | h
  · exact Or.inr (preTilt_dvd_iff_norm_le.2 h)
  · exact Or.inl (preTilt_dvd_iff_norm_le.2 h)

end GlobalTheory.CompanionTheory.TiltFacts
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.LSeq

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem lpow_nzd (n : ℕ) : (l : A.Acr0) ^ n ∈ nonZeroDivisors A.Acr0 :=
  pow_mem (A.acris_torsion_free l (Fact.out : l.Prime).ne_zero) n



def alphaL (n : ℕ) : A.Acr0 →ₗ[A.Acr0] (A.Acr0 ⧸ Ideal.span {(l : A.Acr0) ^ (n + 1)}) :=
  (Submodule.mkQ _).comp (LinearMap.mulLeft A.Acr0 ((l : A.Acr0) ^ n))


set_option synthInstance.maxHeartbeats 400000 in
def alpha (n : ℕ) : A.Acr 1 →+ A.Acr (n + 1) :=
  ((Ideal.span {(l : A.Acr0) ^ 1}).liftQ (alphaL A n) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker]
    simp only [alphaL, LinearMap.comp_apply, LinearMap.mulLeft_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩)).toAddMonoidHom

theorem alpha_mk (n : ℕ) (y : A.Acr0) :
    alpha A n (A.mkAcr 1 y) = A.mkAcr (n + 1) ((l : A.Acr0) ^ n * y) := rfl

theorem alpha_injective (n : ℕ) : Function.Injective (alpha A n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, A.mkAcr 1 y = x := Ideal.Quotient.mk_surjective x
  rw [alpha_mk] at hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  have h0 : (l : A.Acr0) ^ n * (y - c * (l : A.Acr0) ^ 1) = 0 := by
    rw [mul_sub, ← hc]; ring
  have h1 := mem_nonZeroDivisors_iff_left.1 (lpow_nzd A n) _ h0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨c, (sub_eq_zero.1 h1).symm⟩)

theorem alpha_exact (n : ℕ) : Function.Exact (alpha A n) (A.red n.le_succ) := by
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, A.mkAcr (n + 1) y = x := Ideal.Quotient.mk_surjective x
  rw [red_mk]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    exact ⟨A.mkAcr 1 c, by rw [alpha_mk, ← hc, mul_comm]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ : ∃ w, A.mkAcr 1 w = z := Ideal.Quotient.mk_surjective z
    rw [← red_mk A n.le_succ y, ← hz, alpha_mk, red_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨w, mul_comm _ _⟩)

theorem racrSeq (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.D.RAcrSeq l :=
  fun n => ⟨fun A => alpha A n, fun A y => alpha_mk A n y, fun A => ⟨alpha_injective A n, alpha_exact A n⟩⟩

end GlobalTheory.CompanionTheory.LSeq
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Ix (n : ℕ) := Bool × Fin n × Fin n

def hm (p : Ix n) : Mat n :=
  if p.1 then Matrix.single p.2.1 p.2.2 1 + Matrix.single p.2.2 p.2.1 1
  else Matrix.single p.2.1 p.2.2 Complex.I - Matrix.single p.2.2 p.2.1 Complex.I

def sk (p : Ix n) : Mat n :=
  if p.1 then Matrix.single p.2.1 p.2.2 1 - Matrix.single p.2.2 p.2.1 1
  else Matrix.single p.2.1 p.2.2 Complex.I + Matrix.single p.2.2 p.2.1 Complex.I

section Calc

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

def Rr (X : Mat n) (f : Mat n → W) : Mat n → W := fun g => fderiv ℝ f g (g * X)

def Sm (u : ℝ → Mat n → W) : Prop := ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n)

def dt (u : ℝ → Mat n → W) : ℝ → Mat n → W := fun s y => deriv (fun r => u r y) s

def Rt (X : Mat n) (u : ℝ → Mat n → W) : ℝ → Mat n → W := fun s => Rr X (u s)

def dens (u : ℝ → Mat n → W) (s : ℝ) (y : Mat n) : ℝ :=
  ‖dt u s y‖ ^ 2 + (1 / 4) * ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 + ‖u s y‖ ^ 2

end Calc

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : GLs n = (fun g : Mat n => g.det) ⁻¹' {0}ᶜ := by ext g; simp [GLs]
  rw [this]
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det continuous_id)

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  exact this.ne_zero

end GlobalTheory.CompanionTheory.WaveSpd
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Mol.HfSmooth

theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y i j) :=
  contDiff_apply_apply ℝ i j

theorem contDiff_det {n : ℕ} {M : Mat n → Mat n} (hM : ∀ i j, ContDiff ℝ ∞ (fun y => M y i j)) :
    ContDiff ℝ ∞ (fun y => (M y).det) := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => hM _ _

theorem contDiff_adjugate_entry {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ∞ (fun y : Mat n => y.adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det fun a b => ?_
  by_cases h : a = j
  · subst h
    simpa [Matrix.updateRow_self] using contDiff_const
  · simpa [Matrix.updateRow_ne h] using contDiff_entry a b

theorem contDiffOn_inv {n : ℕ} : ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹) (GLs n) := by
  have hd : ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹) (GLs n) :=
    (contDiff_det (M := id) contDiff_entry).contDiffOn.inv (fun y hy => hy)
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  refine (hd.mul (contDiff_adjugate_entry i j).contDiffOn).congr fun y _ => ?_
  simp [Matrix.inv_def, Ring.inverse_eq_inv]

end GlobalTheory.CompanionTheory.WaveCp.Rep.Mol.HfSmooth
end
end
