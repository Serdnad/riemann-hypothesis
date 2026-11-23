module

public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.Places
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.ModuleFiniteHomRep
import GroundTheory.GlobalFields.SUnits
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GEqAddOfExactOfFiniteCokernel
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.Bundle001
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Kummer
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.OrbitInvariants
import GroundTheory.ProfiniteCohomology.RestrictedRamification.MulDistribMulActionGalUnitsFiniteSubfield
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Bundle003
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Additive
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]

omit [Normal K.1 L.1] in
theorem module_finite_S_units [Finite S] : Module.Finite ℤ (AA hL 0) := by
  have : Finite (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) := finite_placesOver (L := L.1) (S := S)
  exact Module.Finite.equiv (gsH0SUnitsEquiv hL).symm.toIntLinearEquiv

omit [Normal K.1 L.1] in
theorem finite_H1_S_units : Finite (AA hL 1) := finite_gsH1SUnits hL

theorem finite_modN_AA [Finite S] (i : ℕ) (hi : i ≤ 1) : Finite (ModN (AA hL i) ℓ) := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  interval_cases i
  · have := module_finite_S_units hL
    exact finite_modN_of_moduleFinite ℓ
  · have := finite_H1_S_units hL
    exact Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)

theorem finite_torsN_AA [Finite S] (i : ℕ) (hi : i ≤ 1) : Finite (TorsN (AA hL i) ℓ) := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  interval_cases i
  · have := module_finite_S_units hL
    exact finite_torsN_of_moduleFinite ℓ
  · have := finite_H1_S_units hL
    exact Subtype.finite

theorem card_gal_eq_index : Nat.card (L.1 ≃ₐ[K.1] L.1) =
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index := by
  rw [Subgroup.index]
  exact (Nat.card_congr (gsQuotientGalEquiv hL).toEquiv).symm

end PositivityTheory.Lit1.GEN.X
end

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global
open scoped TensorProduct

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

section Helpers

variable {k Γ Δ V : Type*} [CommRing k] [Group Γ] [Group Δ] [AddCommGroup V] [Module k V]

theorem invariants_comp_surjective (σ : Representation k Γ V) (f : Δ →* Γ)
    (hf : Function.Surjective f) : Representation.invariants (σ.comp f) = σ.invariants := by
  ext n
  simp only [Representation.mem_invariants, MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · intro h g
    obtain ⟨d, rfl⟩ := hf g
    exact h d
  · intro h d
    exact h (f d)

theorem invariants_comp_subtype_top (σ : Representation k Γ V) (R : Subgroup Γ)
    (hR : ∀ γ, γ ∈ R) : Representation.invariants (σ.comp R.subtype) = σ.invariants :=
  invariants_comp_surjective σ R.subtype fun γ => ⟨⟨γ, hR γ⟩, rfl⟩

theorem invariants_comp_equiv_map (σ : Representation k Γ V) (e : Γ ≃* Δ) (R : Subgroup Γ)
    (D : Subgroup Δ) (hD : R.map e.toMonoidHom = D) :
    Representation.invariants ((σ.comp e.symm.toMonoidHom).comp D.subtype) =
      Representation.invariants (σ.comp R.subtype) := by
  ext n
  simp only [Representation.mem_invariants, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h r
    have hm : e r.1 ∈ D := by
      rw [← hD]
      exact ⟨r.1, r.2, rfl⟩
    have := h ⟨e r.1, hm⟩
    simpa using this
  · intro h d
    have hm : d.1 ∈ R.map e.toMonoidHom := by rw [hD]; exact d.2
    obtain ⟨r, hr, hrd⟩ := hm
    have := h ⟨r, hr⟩
    simp only at this
    rw [← hrd]
    simpa using this

theorem finrank_invariants_trivial_tprod {k Γ N : Type} [CommRing k] [Group Γ] [AddCommGroup N]
    [Module k N] (σ : Representation k Γ N) :
    Module.finrank k ((Representation.trivial k Γ (ULift.{0} k)).tprod σ).invariants =
      Module.finrank k σ.invariants := by
  let eT : ULift.{0} k ⊗[k] N ≃ₗ[k] N :=
    (TensorProduct.congr ULift.moduleEquiv (LinearEquiv.refl _ _)).trans (TensorProduct.lid _ _)
  refine finrank_invariants_eq_of_linearEquiv _ eT fun g x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => simp [eT, Representation.tprod_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Helpers

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]
  (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
  (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)
  (hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ)

theorem global_dual_invariants_finrank (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    (Module.finrank (ZMod ℓ) (dualRep (gsRootsZMod S ℓ) M).ρ.invariants : ℤ) = (dN hL hζ M hM hΓ).one := by
  classical
  have hT : Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ) = 1 := finrank_gsRootsZMod ℓ hℓS
  have hN := homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM
  have hfin : Finite (galUnramifiedOutside K.1 ℚ̄ S ⧸ PP hL) :=
    Finite.of_equiv _ (gsQuotientGalEquiv hL).symm.toEquiv
  have : Fintype ((QuotientGroup.mk' (PP hL)).comp (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S))).range :=
    Fintype.ofFinite _
  have hD : (Fintype.card ((QuotientGroup.mk' (PP hL)).comp
      (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S))).range : ZMod ℓ) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have h1 := Subgroup.card_subgroup_dvd_card ((QuotientGroup.mk' (PP hL)).comp
      (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S))).range
    have h2 : Nat.card (galUnramifiedOutside K.1 ℚ̄ S ⧸ PP hL) = Nat.card (L.1 ≃ₐ[K.1] L.1) :=
      Nat.card_congr (gsQuotientGalEquiv hL).toEquiv
    rw [h2] at h1
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)).1 hΓ.symm (dvd_trans hdvd h1)
  have key := finrank_invariants_dualRep_comp (gsRootsZMod S ℓ) M hT (PP hL) hN
    (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S)) hD
  have hsurj : ∀ γ, γ ∈ ((QuotientGroup.mk' (PP hL)).comp
      (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S))).range := fun γ => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (PP hL) γ
    exact ⟨x, rfl⟩
  have e1 : Representation.invariants ((dualRep (gsRootsZMod S ℓ) M).ρ.comp
      (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S))) = (dualRep (gsRootsZMod S ℓ) M).ρ.invariants :=
    invariants_comp_surjective (dualRep (gsRootsZMod S ℓ) M).ρ
      (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S)) Function.surjective_id
  have e2 : Representation.invariants ((quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M) hN).comp
      ((QuotientGroup.mk' (PP hL)).comp (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S))).range.subtype) =
      (quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M) hN).invariants :=
    invariants_comp_subtype_top _ _ hsurj
  have key2 : Module.finrank (ZMod ℓ) (dualRep (gsRootsZMod S ℓ) M).ρ.invariants =
      Module.finrank (ZMod ℓ) (quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M) hN).invariants :=
    ((congrArg (fun p : Submodule (ZMod ℓ) _ => Module.finrank (ZMod ℓ) p) e1).symm.trans key).trans
      (congrArg (fun p : Submodule (ZMod ℓ) _ => Module.finrank (ZMod ℓ) p) e2)
  rw [key2]
  have e3 : Representation.invariants (nRep hL hζ M hM) =
      (quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M) hN).invariants := by
    unfold nRep
    exact invariants_comp_surjective _ _ (gsQuotientGalEquiv hL).symm.surjective
  have e4 := finrank_invariants_trivial_tprod (nRep hL hζ M hM)
  have e4' := e4.trans (congrArg (fun p : Submodule (ZMod ℓ) _ => Module.finrank (ZMod ℓ) p) e3)
  have e5 : (dN hL hζ M hM hΓ).one = (Module.finrank (ZMod ℓ)
      ((Representation.trivial (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1) (ULift.{0} (ZMod ℓ))).tprod
        (nRep hL hζ M hM)).invariants : ℤ) :=
    AdditiveFunction.invariantsTensor_apply _ _ _ _ _ _
  exact (congrArg (Nat.cast : ℕ → ℤ) e4'.symm).trans e5.symm

theorem local_dual_invariants_sum [Fintype S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :
    ∑ v : S, (Module.finrank (ZMod ℓ) (Representation.invariants
          ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)) : ℤ) =
      dPlaces (S := S) (dN hL hζ M hM hΓ) := by
  classical
  have hT : Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ) = 1 := finrank_gsRootsZMod ℓ hℓS
  have hN := homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM
  have hfin : Finite (galUnramifiedOutside K.1 ℚ̄ S ⧸ PP hL) :=
    Finite.of_equiv _ (gsQuotientGalEquiv hL).symm.toEquiv
  have hv : ∀ v : S, Module.finrank (ZMod ℓ) (Representation.invariants
      ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)) =
      Module.finrank (ZMod ℓ) (Representation.invariants
        ((nRep hL hζ M hM).comp (gsDecompGroup hL ιs v).subtype)) := by
    intro v
    have : Fintype ((QuotientGroup.mk' (PP hL)).comp (gsFinFamily S ιs v).toMonoidHom).range :=
      Fintype.ofFinite _
    have hD : (Fintype.card ((QuotientGroup.mk' (PP hL)).comp
        (gsFinFamily S ιs v).toMonoidHom).range : ZMod ℓ) ≠ 0 := by
      rw [← Nat.card_eq_fintype_card, Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have h1 := Subgroup.card_subgroup_dvd_card ((QuotientGroup.mk' (PP hL)).comp
        (gsFinFamily S ιs v).toMonoidHom).range
      have h2 : Nat.card (galUnramifiedOutside K.1 ℚ̄ S ⧸ PP hL) = Nat.card (L.1 ≃ₐ[K.1] L.1) :=
        Nat.card_congr (gsQuotientGalEquiv hL).toEquiv
      rw [h2] at h1
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)).1 hΓ.symm (dvd_trans hdvd h1)
    have key := finrank_invariants_dualRep_comp (gsRootsZMod S ℓ) M hT (PP hL) hN
      (gsFinFamily S ιs v).toMonoidHom hD
    have e := invariants_comp_equiv_map (quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M) hN)
      (gsQuotientGalEquiv hL) _ _ (map_range_gsQuotientGalEquiv hL ιs v)
    exact key.trans (congrArg (fun p : Submodule (ZMod ℓ) _ => Module.finrank (ZMod ℓ) p) e.symm)
  have hsum : (letI := placesOverAction (L := L.1) S
      Module.finrank (ZMod ℓ) ((funPermRep (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1)
        (placesOver S : Set (HeightOneSpectrum (𝓞 L.1)))).tprod (nRep hL hζ M hM)).invariants) =
      ∑ v : S, Module.finrank (ZMod ℓ) (Representation.invariants
        ((nRep hL hζ M hM).comp (gsDecompGroup hL ιs v).subtype)) :=
    finrank_invariants_funPermRep_placesOver (hL := hL) (ιs := ιs) (σN := nRep hL hζ M hM)
  have hP : dPlaces (S := S) (dN hL hζ M hM hΓ) = ((letI := placesOverAction (L := L.1) S
      Module.finrank (ZMod ℓ) ((funPermRep (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1)
        (placesOver S : Set (HeightOneSpectrum (𝓞 L.1)))).tprod (nRep hL hζ M hM)).invariants : ℕ) : ℤ) :=
    rfl
  refine Eq.trans ?_ hP.symm
  refine Eq.trans ?_ (congrArg (Nat.cast : ℕ → ℤ) hsum).symm
  refine Eq.trans ?_ (Nat.cast_sum _ _).symm
  exact Finset.sum_congr rfl fun v _ => congrArg (Nat.cast : ℕ → ℤ) (hv v)
end PositivityTheory.Lit1.GEN.X
end

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]
  (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
  (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)
  (hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ)

theorem cast_sum_add_mul {ι : Type*} [Fintype ι] (f : ι → ℕ) (c n m : ℕ) (h : n = m) :
    (((∑ i, f i) + c * n : ℕ) : ℤ) = ∑ i, (f i : ℤ) + (c : ℤ) * (m : ℤ) := by
  subst h; push_cast; rfl


open scoped Classical in
theorem dInf_eq (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    dInf (dN hL hζ M hM hΓ) =
      ∑ v : {v : InfinitePlace K.1 // v.IsReal},
          (Module.finrank (ZMod ℓ) (Representation.invariants
            ((nRep hL hζ M hM).comp (gsRealDecompGroup S ιr hL v).subtype)) : ℤ) +
        Fintype.card {v : InfinitePlace K.1 // v.IsComplex} * Module.finrank (ZMod ℓ) M := by
  have : IsGalois K.1 L.1 := ⟨⟩
  have hT : Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ) = 1 := finrank_gsRootsZMod ℓ hℓS
  have hN : Module.finrank (ZMod ℓ) (homRep (gsRootsZMod S ℓ) M) = Module.finrank (ZMod ℓ) M := by
    change Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ →ₗ[ZMod ℓ] M) = _
    rw [Module.finrank_linearMap, hT, one_mul]
  have key := finrank_invariants_funPermRep_infinitePlace (k := ZMod ℓ) S ιr hL (nRep hL hζ M hM)
  have e1 : dInf (dN hL hζ M hM hΓ) = (Module.finrank (ZMod ℓ) ((funPermRep (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1)
        (NumberField.InfinitePlace L.1)).tprod (nRep hL hζ M hM)).invariants : ℤ) :=
    AdditiveFunction.invariantsTensor_apply _ _ _ _ _ _
  exact e1.trans ((congrArg (Nat.cast (R := ℤ)) key).trans (cast_sum_add_mul _ _ _ _ hN))

end PositivityTheory.Lit1.GEN.X
end

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]

theorem units_finite_modN_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (n : ℕ)
    [Finite (ModN A n)] : Finite (ModN B n) := by
  have h : LinearMap.range (LinearMap.lsmul ℤ A (n : ℤ)) ≤
      (LinearMap.range (LinearMap.lsmul ℤ B (n : ℤ))).comap e.toIntLinearEquiv.toLinearMap := by
    rintro _ ⟨y, rfl⟩
    exact ⟨e y, by simp⟩
  refine Finite.of_surjective (Submodule.mapQ _ _ e.toIntLinearEquiv.toLinearMap h) fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | H b => exact ⟨Submodule.Quotient.mk (e.symm b), by simp⟩

theorem units_finite_torsN_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (n : ℕ)
    [Finite (TorsN A n)] : Finite (TorsN B n) := by
  refine Finite.of_surjective (fun x : TorsN A n => (⟨e x.1, by
    have hx := (mem_ker_lsmul_iff n (x : A)).1 x.2
    exact (mem_ker_lsmul_iff n (e x.1)).2 (by rw [← map_nsmul, hx, map_zero])⟩ : TorsN B n)) fun y => ?_
  refine ⟨⟨e.symm y.1, (mem_ker_lsmul_iff n _).2 ?_⟩, ?_⟩
  · rw [← map_nsmul, (mem_ker_lsmul_iff n (y : B)).1 y.2, map_zero]
  · ext; simp

theorem S_units_euler_difference [Finite S] (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1))
    [Finite (ModN (AA hL 0) ℓ)] [Finite (TorsN (AA hL 0) ℓ)] :
    dMod hL d 0 - dTors hL d 0 = dPlaces (S := S) d + dInf d - d.one := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : Finite (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) := finite_placesOver (L := L.1) (S := S)
  haveI : Finite (ModN (Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L.1))).unit L.1)) ℓ) :=
    units_finite_modN_of_addEquiv (gsH0SUnitsEquiv hL) ℓ
  haveI : Finite (TorsN (Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L.1))).unit L.1)) ℓ) :=
    units_finite_torsN_of_addEquiv (gsH0SUnitsEquiv hL) ℓ
  have hU := conj_gsH0SUnits_eq hL d
  have hg : (letI := actA hL 0; d.g (AA hL 0)) = dMod hL d 0 - dTors hL d 0 := by
    letI := actA hL 0
    exact d.g_eq _
  have hS := d.g_sUnits (placesOver S : Set (HeightOneSpectrum (𝓞 L.1)))
    (placesOver_stable (S := S) (K := K) (L := L))
  rw [← hg]
  exact hU.trans hS

theorem class_group_mod_eq_torsion [Finite S] (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1))
    [Finite (ModN (AA hL 1) ℓ)] [Finite (TorsN (AA hL 1) ℓ)] :
    dMod hL d 1 = dTors hL d 1 := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  letI := actA hL 1
  haveI : Finite (AA hL 1) := finite_gsH1SUnits hL
  have h1 := d.g_eq_zero_of_finite (AA hL 1)
  rw [d.g_eq (AA hL 1)] at h1
  unfold dMod dTors
  exact sub_eq_zero.1 h1

end PositivityTheory.Lit1.GEN.X
end
