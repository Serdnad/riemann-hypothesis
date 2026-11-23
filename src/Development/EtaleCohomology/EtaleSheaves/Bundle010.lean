module

public import Development.EtaleCohomology.EtaleSheaves.Bundle005
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.EtAICPf

def Split : Prop := ∀ (T C : Type) [CommRing T] [IsDomain T] [CommRing C] [Algebra T C] [Algebra.Etale T C], AIC T →
  ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j, IsDomain (Localization.Away (e j))

def DomOpen : Prop := ∀ (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D] [Algebra.Etale T D],
  AIC T → IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap T D)))

theorem EtAIC_of (hS : Split) (hD : DomOpen) : LateralTheory.E.t_E1Cut.EtAIC := by
  intro T C _ _ _ _ _ hT
  obtain ⟨n, e, he, hdom⟩ := hS T C hT
  refine ⟨n, e, he, fun j => ?_⟩
  have : Algebra.Etale C (Localization.Away (e j)) := inferInstance
  have : Algebra.Etale T (Localization.Away (e j)) := Algebra.Etale.comp T C _
  have h := hD T (Localization.Away (e j)) hT
  rwa [IsScalarTower.algebraMap_eq T C (Localization.Away (e j))] at h

end LateralTheory.E.EtAICPf
end
end

section

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.QAClosedPf

open LateralTheory.E.t_E1Cut

theorem aic_of_surj {T S : Type} [CommRing T] [CommRing S] (π : T →+* S) (hT : AIC T)
    (hπ : Function.Surjective π) : AIC S := by
  intro p hp hdeg
  have hl : p ∈ lifts π := (lifts_iff_coeff_lifts p).2 fun n => hπ _
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hp
  obtain ⟨a, ha⟩ := hT q hqm (hqd ▸ hdeg)
  refine ⟨π a, ?_⟩
  rw [← hq, eval_map, eval₂_at_apply, ha, map_zero]

theorem aic_away {T : Type} [CommRing T] [IsDomain T] (hT : AIC T) (t : T) (ht : t ≠ 0) :
    AIC (Localization.Away t) := by
  classical
  have : IsDomain (Localization.Away t) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  intro p hp hdeg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (Submonoid.powers t)
    (p.support.image p.coeff)
  set c : Localization.Away t := algebraMap T _ b
  have hcu : IsUnit c := IsLocalization.map_units _ b
  have hl : p.scaleRoots c ∈ lifts (algebraMap T (Localization.Away t)) := by
    refine (lifts_iff_coeff_lifts _).2 fun i => ?_
    rw [coeff_scaleRoots]
    by_cases hi : i ∈ p.support
    · have hle : i ≤ p.natDegree := le_natDegree_of_mem_supp i hi
      rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨z, hz⟩ := hb _ (Finset.mem_image_of_mem _ hi)
        refine ⟨z * b ^ (p.natDegree - i - 1), ?_⟩
        rw [map_mul, hz, Algebra.smul_def, map_pow]
        rw [show c ^ (p.natDegree - i) = c * c ^ (p.natDegree - i - 1) by
          rw [← pow_succ']; congr 1; omega]
        simp only [c]
        ring
      · subst heq
        refine ⟨1, ?_⟩
        rw [hp.coeff_natDegree, Nat.sub_self, pow_zero, one_mul, map_one]
    · rw [Polynomial.notMem_support_iff.1 hi]
      exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff c).2 hp)
  rw [natDegree_scaleRoots] at hqd
  obtain ⟨a, ha⟩ := hT q hqm (hqd ▸ hdeg)
  refine ⟨hcu.unit⁻¹ * algebraMap T _ a, ?_⟩
  have h1 : eval (algebraMap T _ a) (p.scaleRoots c) = 0 := by
    rw [← hq, eval_map, eval₂_at_apply, ha, map_zero]
  have h2 : algebraMap T (Localization.Away t) a = (RingHom.id _) c * (hcu.unit⁻¹ * algebraMap T _ a) := by
    rw [RingHom.id_apply, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  rw [eval, h2, scaleRoots_eval₂_mul] at h1
  rw [eval]
  exact (mul_eq_zero.1 h1).resolve_left (by simpa using (hcu.pow _).ne_zero)

theorem QAClosed_of : QAClosed := by
  intro S _ hS
  obtain ⟨T, _, _, π, hT, hπ⟩ := hS
  refine ⟨aic_of_surj π hT hπ, ?_, ?_⟩
  · intro f
    obtain ⟨t, rfl⟩ := hπ f
    by_cases ht : t = 0
    · have hu : IsUnit (algebraMap S (Localization.Away (π t)) (π t)) :=
        IsLocalization.Away.algebraMap_isUnit _
      rw [show algebraMap S (Localization.Away (π t)) (π t) = 0 by rw [ht, map_zero, map_zero]] at hu
      have : Subsingleton (Localization.Away (π t)) := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu)
      exact ⟨T, inferInstance, inferInstance, (algebraMap S _).comp π, hT, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
    · have : IsDomain (Localization.Away t) :=
        IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
      have : IsLocalization (Submonoid.map π (Submonoid.powers t)) (Localization.Away (π t)) := by
        rw [Submonoid.map_powers]; infer_instance
      exact ⟨Localization.Away t, inferInstance, inferInstance, _, aic_away hT t ht,
        IsLocalization.map_surjective_of_surjective (Submonoid.powers t) (Localization.Away t)
          (Localization.Away (π t)) hπ⟩
  · intro J
    exact ⟨T, inferInstance, inferInstance, (Ideal.Quotient.mk J).comp π, hT,
      (Ideal.Quotient.mk_surjective).comp hπ⟩

end LateralTheory.E.QAClosedPf
end
end

section

noncomputable section
open MvPolynomial

namespace LateralTheory.E.EtLiftPf

set_option linter.style.haveILetI false

theorem EtLift_of : LateralTheory.E.t_E1Cut.EtLift := by
  intro T S C _ _ _ _ _ π hπ
  letI : Algebra T S := π.toAlgebra
  letI : Algebra T C := ((algebraMap S C).comp π).toAlgebra
  haveI : IsScalarTower T S C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨ι, σ, _, _, P, hP⟩ := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1 ‹_›).out
  haveI : P.HasCoeffs T := ⟨fun x _ => hπ x⟩
  let M := P.ModelOfHasCoeffs T
  let P0 := P.toPreSubmersivePresentation.ofHasCoeffs T
  let J : M := P0.jacobian
  let C' := Localization.Away J
  let Q := Algebra.PreSubmersivePresentation.localizationAway C' J
  let R0 := Q.comp P0
  have hJu : IsUnit (algebraMap M C' J) := IsLocalization.Away.algebraMap_isUnit J
  have hJ : R0.jacobian = algebraMap M C' J * algebraMap M C' J := by
    simp only [R0, Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Q,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    rfl
  let R1 : Algebra.SubmersivePresentation T C' (Unit ⊕ ι) (Unit ⊕ σ) :=
    { R0 with jacobian_isUnit := by rw [hJ]; exact hJu.mul hJu }
  have hdim : R1.dimension = 0 := by
    have := Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension Q P0
    have hQ : Q.dimension = 0 := Algebra.Presentation.localizationAway_dimension_zero J
    have hP0 : P0.dimension = 0 := hP
    exact this.trans (by rw [hQ, hP0])
  haveI : Algebra.Etale T C' := by
    haveI := R1.isStandardSmoothOfRelativeDimension hdim
    infer_instance

  let φM : M →ₐ[T] C := Ideal.Quotient.liftₐ _ (MvPolynomial.aeval P.val) (by
    intro a ha
    have hle : Ideal.span (Set.range (P.relationOfHasCoeffs T)) ≤
        RingHom.ker (MvPolynomial.aeval (R := T) P.val) := by
      rw [Ideal.span_le]; rintro _ ⟨r, rfl⟩
      exact P.toPresentation.aeval_val_relationOfHasCoeffs T r
    exact hle ha)
  have hφmk : ∀ p : MvPolynomial ι T, φM (Ideal.Quotient.mk _ p) = MvPolynomial.aeval P.val p :=
    fun p => rfl
  have hφJ : φM J = P.jacobian := by
    classical
    cases nonempty_fintype σ
    rw [← P.aeval_jacobianOfHasCoeffs T]
    show φM P0.jacobian = _
    rw [P0.jacobian_eq_jacobiMatrix_det]
    unfold Algebra.SubmersivePresentation.jacobianOfHasCoeffs
    exact (hφmk _).trans (by congr 1; convert rfl)
  let ρ : C' →+* C := IsLocalization.Away.lift J (hφJ ▸ P.jacobian_isUnit)
  have hρM : ∀ m : M, ρ (algebraMap M C' m) = φM m := fun m => IsLocalization.lift_eq _ m
  refine ⟨C', inferInstance, inferInstance, ρ, inferInstance, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨q, hq⟩ := MvPolynomial.map_surjective π hπ (P.σ c)
    refine ⟨algebraMap M C' (Ideal.Quotient.mk _ q), ?_⟩
    rw [hρM, hφmk, ← MvPolynomial.aeval_map_algebraMap S]
    change MvPolynomial.aeval P.val (MvPolynomial.map π q) = c
    rw [hq, P.aeval_val_σ]
  · ext t
    show ρ (algebraMap T C' t) = _
    rw [IsScalarTower.algebraMap_apply T M C', hρM, AlgHom.commutes]
    rfl
  · let K : Ideal C' := (RingHom.ker π).map (algebraMap T C')
    have hT : ∀ t, ρ (algebraMap T C' t) = algebraMap S C (π t) := by
      intro t; rw [IsScalarTower.algebraMap_apply T M C', hρM, AlgHom.commutes]; rfl
    apply le_antisymm
    swap
    · rw [Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap, RingHom.mem_ker, hT, RingHom.mem_ker.1 ht, map_zero]
    let e := RingHom.quotientKerEquivOfSurjective hπ
    let θ : S →+* C' ⧸ K :=
      (Ideal.quotientMap K (algebraMap T C') Ideal.le_comap_map).comp e.symm.toRingHom
    have hθ : ∀ t, θ (π t) = Ideal.Quotient.mk K (algebraMap T C' t) := by
      intro t
      have : e.symm (π t) = Ideal.Quotient.mk _ t := by
        rw [RingEquiv.symm_apply_eq]; rfl
      show Ideal.quotientMap K (algebraMap T C') Ideal.le_comap_map (e.symm (π t)) = _
      rw [this, Ideal.quotientMap_mk]
    let xv : ι → C' ⧸ K := fun i => Ideal.Quotient.mk K (algebraMap M C' (Ideal.Quotient.mk _ (X i)))
    let χ : MvPolynomial ι S →+* C' ⧸ K := MvPolynomial.eval₂Hom θ xv
    have hkey : ∀ q : MvPolynomial ι T, χ (MvPolynomial.map π q) =
        Ideal.Quotient.mk K (algebraMap M C' (Ideal.Quotient.mk _ q)) := by
      intro q
      have h2 : χ.comp (MvPolynomial.map π) =
          ((Ideal.Quotient.mk K).comp (algebraMap M C')).comp (Ideal.Quotient.mk _) := by
        apply MvPolynomial.ringHom_ext
        · intro t
          simp only [RingHom.comp_apply, MvPolynomial.map_C, χ, MvPolynomial.coe_eval₂Hom,
            MvPolynomial.eval₂_C, hθ]
          rw [IsScalarTower.algebraMap_apply T M C']
          rfl
        · intro i
          simp [χ, xv]
      exact RingHom.congr_fun h2 q
    have hker : ∀ a ∈ P.ker, χ a = 0 := by
      intro a ha
      rw [← P.span_range_relation_eq_ker] at ha
      have hle : Ideal.span (Set.range P.relation) ≤ RingHom.ker χ := by
        rw [Ideal.span_le]; rintro _ ⟨r, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, ← P.toPresentation.map_relationOfHasCoeffs T r]
        change χ (MvPolynomial.map π _) = 0
        rw [hkey, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self r)), map_zero, map_zero]
      exact hle ha
    let ψ : C →+* C' ⧸ K := (Ideal.Quotient.lift P.ker χ hker).comp P.quotientEquiv.symm.toRingHom
    have hψP : ∀ p, ψ (algebraMap P.Ring C p) = χ p := by
      intro p
      show Ideal.Quotient.lift P.ker χ hker (P.quotientEquiv.symm (algebraMap _ _ p)) = χ p
      rw [← P.quotientEquiv_mk, AlgEquiv.symm_apply_apply]
      rfl
    have hψ : ψ.comp ρ = Ideal.Quotient.mk K := by
      apply IsLocalization.ringHom_ext (Submonoid.powers J)
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun q => ?_
      simp only [RingHom.comp_apply]
      rw [hρM, hφmk, ← MvPolynomial.aeval_map_algebraMap S, ← hkey, ← hψP,
        Algebra.Generators.algebraMap_apply]
      rfl
    intro z hz
    rw [RingHom.mem_ker] at hz
    have h3 := RingHom.congr_fun hψ z
    simp only [RingHom.comp_apply, hz, map_zero] at h3
    exact Ideal.Quotient.eq_zero_iff_mem.1 h3.symm
end EtLiftPf
end E
end LateralTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut

namespace LateralTheory.E.AcycQAPf

def MVHyp (q : ℕ) (i n : ℤ) : Prop := ∀ (S : Type) [CommRing S], QA S → IsUnit (q : S) → ∀ f g : S,
  Ideal.span {f, g} = ⊤ → ∀ c : Ht q (sp (Localization.Away (f * g))) n i,
    ∃ a b, c = pull _ (spMap (rL f g)) _ n a - pull _ (spMap (rR f g)) _ n b

def Deg0 : Prop := QAClosed → EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions → LCSplit → A9 → ∀ (q : ℕ) [NeZero q] (i : ℤ), MVHyp q i 0

def Cover : Prop := QAClosed → MV → A1 → ∀ (q : ℕ) [NeZero q] (i n : ℤ), MVHyp q i n → ∀ (S : Type) [CommRing S], QA S → IsUnit (q : S) →
  ∀ x : Ht q (sp S) (n + 1) i, (∀ p : PrimeSpectrum S, ∃ f : S, f ∉ p.asIdeal ∧
    pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0) → x = 0

theorem step (hQ : QAClosed) (hZ : ZarLocal) (hM : MV) (hC : Cover) (h1 : A1) (b1 : B1) (b2 : B2) (q : ℕ) [NeZero q] (i : ℤ) :
    ∀ k : ℕ, MVHyp q i k → ∀ (S : Type) [CommRing S], QA S → IsUnit (q : S) →
      Subsingleton (Ht q (sp S) ((k : ℤ) + 1) i) := by
  intro k hk S _ hS hq
  refine subsingleton_of_forall_eq 0 fun x => ?_
  refine hC hQ hM h1 q i k hk S hS hq x fun p => ?_
  exact hZ b1 b2 q S (hQ S hS).1 hq _ i (by omega) x p

theorem AcycQA_of (hQ : QAClosed) (hZ : ZarLocal) (hM : MV) (hH : EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions) (hL : LCSplit) (hD : Deg0) (hC : Cover) :
    AcycQA := by
  intro h1 h9 b1 b2 q _ S _ hS hq
  have key : ∀ k : ℕ, MVHyp q 0 k ∧ ∀ (i : ℤ), MVHyp q i k := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using hD hQ hH hL h9 q 0, fun i => by simpa using hD hQ hH hL h9 q i⟩
    | succ k ih =>
      have hv : ∀ (i : ℤ), MVHyp q i ((k + 1 : ℕ) : ℤ) := by
        intro i S' _ hS' hq' f g _ c
        have hfg : QA (Localization.Away (f * g)) := (hQ S' hS').2.1 (f * g)
        have hqfg : IsUnit (q : Localization.Away (f * g)) := by
          simpa using hq'.map (algebraMap S' (Localization.Away (f * g)))
        have hs := step hQ hZ hM hC h1 b1 b2 q i k (ih.2 i) _ hfg hqfg
        refine ⟨0, 0, ?_⟩
        have : c = 0 := by
          have e : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
          revert c; rw [e]; intro c; exact Subsingleton.elim _ _
        simp [this]
      exact ⟨hv 0, hv⟩
  intro n i hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  exact step hQ hZ hM hC h1 b1 b2 q i k ((key k).2 i) S hS hq

end LateralTheory.E.AcycQAPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.FinEtSectionPf

def Pieces : Prop := LateralTheory.E.t_E1Cut.EtLift → LateralTheory.E.t_E1Cut.EtAIC → ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Algebra.Etale S C], LateralTheory.E.t_E1Cut.QA S →
  ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j,
    IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C))))

def FinOpen : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] (e : C), IsIdempotentElem e →
  IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away e)).comp (algebraMap S C)))) →
  ∃ ε : S, IsIdempotentElem ε ∧
    Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away e)).comp (algebraMap S C))) =
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum S)) ∧
    ∃ h : Localization.Away e →+* Localization.Away ε,
      h.comp ((algebraMap C (Localization.Away e)).comp (algebraMap S C)) = algebraMap S (Localization.Away ε)

def Glue : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] (n : ℕ) (e : Fin n → C),
  CompleteOrthogonalIdempotents e → Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) →
  ∀ ε : Fin n → S, (∀ j, IsIdempotentElem (ε j)) →
  (∀ j, Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C))) =
      (PrimeSpectrum.basicOpen (ε j) : Set (PrimeSpectrum S))) →
  (∀ j, ∃ h : Localization.Away (e j) →+* Localization.Away (ε j),
      h.comp ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C)) = algebraMap S (Localization.Away (ε j))) →
  Nonempty (C →ₐ[S] S)

theorem FinEtSection_of (hL : LateralTheory.E.t_E1Cut.EtLift) (hA : LateralTheory.E.t_E1Cut.EtAIC) (hP : Pieces) (hF : FinOpen) (hG : Glue) : LateralTheory.E.t_E1Cut.FinEtSection := by
  intro S C _ _ _ _ _ hQA hsurj
  obtain ⟨n, e, he, hoi⟩ := hP hL hA S C hQA
  choose ε hε hr hh using fun j => hF S C (e j) (he.idem j) (hoi j)
  exact hG S C n e he hsurj ε hε hr hh

end LateralTheory.E.FinEtSectionPf
end
end

section

noncomputable section
open Polynomial

namespace LateralTheory.E.HensIdemCut

def LJac : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (B : Type) [CommRing B] (φ : A →+* B),
  φ.IsIntegral → I.map φ ≤ Ideal.jacobson ⊥

def LMonic : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (B : Type) [CommRing B] (φ : A →+* B),
  φ.IsIntegral → ∀ b : B, b * b - b ∈ I.map φ → ∃ (N : ℕ) (f : A[X]), f.Monic ∧ f.eval₂ φ b = 0 ∧
    f.map (Ideal.Quotient.mk I) = X ^ N * (X - C 1) ^ N

def LFactor : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (f : A[X]) (g₀ h₀ : (A ⧸ I)[X]),
  f.Monic → g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ → f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
  ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧ g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀

def LIdem : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (B : Type) [CommRing B] (φ : A →+* B),
  I.map φ ≤ Ideal.jacobson ⊥ → ∀ (b : B), b * b - b ∈ I.map φ → ∀ (N : ℕ) (g h : A[X]),
  g.map (Ideal.Quotient.mk I) = X ^ N → h.map (Ideal.Quotient.mk I) = (X - C 1) ^ N →
  g.eval₂ φ b * h.eval₂ φ b = 0 → ∃ x : B, IsIdempotentElem x ∧ x - b ∈ I.map φ

theorem goal_of (hJ : LJac) (hM : LMonic) (hF : LFactor) (hI : LIdem) : LateralTheory.E.t_E1Cut.HensIdem := by
  intro A _ I _ B _ φ hφ
  refine ⟨hJ A I B φ hφ, ?_⟩
  intro e he
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective e
  have hb : b * b - b ∈ I.map φ := by
    rw [← Ideal.Quotient.eq]
    simpa [IsIdempotentElem] using he
  obtain ⟨N, f, hfm, hf0, hfI⟩ := hM A I B φ hφ b hb
  have hcop : IsCoprime ((X : (A ⧸ I)[X]) ^ N) ((X - C 1) ^ N) :=
    (show IsCoprime (X : (A ⧸ I)[X]) (X - C 1) from ⟨1, -1, by rw [C_1]; ring⟩).pow
  obtain ⟨g, h, -, -, rfl, hg, hh⟩ :=
    hF A I f _ _ hfm ((monic_X).pow N) ((monic_X_sub_C 1).pow N) hcop hfI
  obtain ⟨x, hx, hxb⟩ := hI A I B φ (hJ A I B φ hφ) b hb N g h hg hh (by rw [← eval₂_mul]; exact hf0)
  exact ⟨x, hx, Ideal.Quotient.eq.mpr hxb⟩

end LateralTheory.E.HensIdemCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.MVPf

def MVSpc : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ n : ℤ, (∀ c : H R (pullback f g) F n, ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) →
  ∀ x : H R E F (n + 1), pull R f F _ x = 0 → pull R g F _ x = 0 → x = 0

def StdCover : Prop := ∀ (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  Cover2 R (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g)))

def StdPB : Prop := ∀ (S : Type) [CommRing S] (f g : S),
  ∃ e : sp (Localization.Away (f * g)) ⟶
      pullback (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g))),
    IsIso e ∧ e ≫ pullback.fst _ _ = spMap (LateralTheory.E.t_E1Cut.rL f g) ∧ e ≫ pullback.snd _ _ = spMap (LateralTheory.E.t_E1Cut.rR f g)

theorem pull_inj_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) :
    Function.Injective (pull R e F n) := by
  intro x y h
  have hx : pull R (inv e) F n (pull R e F n x) = x := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have hy : pull R (inv e) F n (pull R e F n y) = y := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  rw [← hx, ← hy, h]

end LateralTheory.E.MVPf

open LateralTheory.E.MVPf in
theorem LateralTheory.E.t_E1Cut.MV_of (h1 : MVSpc) (h2 : StdCover) (h3 : StdPB) : LateralTheory.E.t_E1Cut.MV := by
  intro hA1 R _ F S _ f g hfg n hc x hxf hxg
  refine h1 hA1 R F _ _ (h2 R S f g hfg) n ?_ x hxf hxg
  intro c
  obtain ⟨e, he, hfst, hsnd⟩ := h3 S f g
  obtain ⟨a, b, hab⟩ := hc (pull R e F n c)
  refine ⟨a, b, pull_inj_of_iso R e F n ?_⟩
  rw [hab, map_sub, ← pull_comp, ← pull_comp, hfst, hsnd]
end
end
