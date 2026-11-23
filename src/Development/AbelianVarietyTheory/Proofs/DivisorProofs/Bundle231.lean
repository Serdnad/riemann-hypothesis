module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle125
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle124
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Unramified.Finite
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory.EtaleHensel

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem algHom_eq_of_residue_eq [Algebra.Etale R A] [IsLocalRing B] {φ₁ φ₂ : A →ₐ[R] B}
    (h : ∀ a, residue B (φ₁ a) = residue B (φ₂ a)) : φ₁ = φ₂ := by

  obtain ⟨t, ht, ht1⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).mp inferInstance
  let ψ : TensorProduct R A A →ₐ[R] B := Algebra.TensorProduct.productMap φ₁ φ₂
  let ρ : B →ₐ[R] ResidueField B := IsScalarTower.toAlgHom R B (ResidueField B)
  have hρ : ∀ b, ρ b = residue B b := fun _ => rfl
  have key : ρ.comp ψ = (ρ.comp φ₁).comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, ψ, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul, hρ, h b]
  have hres : residue B (ψ t) = 1 := by
    have := congrArg (fun f : TensorProduct R A A →ₐ[R] ResidueField B => f t) key
    simpa only [AlgHom.comp_apply, ht1, map_one, hρ] using this
  have hu : IsUnit (ψ t) := by
    by_contra hn
    have h0 : residue B (ψ t) = 0 := (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn)
    exact one_ne_zero (hres.symm.trans h0)
  ext a
  have hz := congrArg ψ (ht a)
  simp only [map_mul, map_sub, map_zero, ψ, Algebra.TensorProduct.productMap_apply_tmul,
    map_one, one_mul, mul_one] at hz
  exact (sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)).symm

theorem bijective_residue_comp : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Etale R A] [HenselianLocalRing B],
    Function.Bijective
      (fun φ : A →ₐ[R] B => (IsScalarTower.toAlgHom R B (ResidueField B)).comp φ) := by
  intro R A B _ _ _ _ _ _ _
  refine ⟨fun φ₁ φ₂ he => algHom_eq_of_residue_eq fun a => ?_, fun φ => ?_⟩
  · exact DFunLike.congr_fun he a
  · obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_smooth (maximalIdeal B)
      (IsScalarTower.toAlgHom R B (ResidueField B)) residue_surjective
      (fun b => (residue_eq_zero_iff b).symm) φ
    exact ⟨ψ, hψ⟩

end GlobalTheory.EtaleHensel
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etale_localization_atPrime_tensor_of_etale_away' : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (b : R),
    Algebra.Etale R (Localization.Away (algebraMap R C b)) →
    ∀ (P : Ideal R) [P.IsPrime], b ∉ P →
      Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  first | (exact @GlobalTheory.etale_localization_atPrime_tensor_of_etale_away) | (exact GlobalTheory.etale_localization_atPrime_tensor_of_etale_away) | (intros; apply GlobalTheory.etale_localization_atPrime_tensor_of_etale_away <;> assumption)
end

section

open IsLocalRing TensorProduct Pointwise

theorem _root_.GlobalTheory.T.etale_localization_of_injective_cokernel_killed : ∀ (S : Type) [CommRing S] (A B : Type) [CommRing A] [CommRing B] [Algebra S A] [Algebra S B] (ι : A →ₐ[S] B), Function.Injective ι → ∀ (p : Ideal S) [p.IsPrime] (s : S), s ∉ p → (∀ y : B, s • y ∈ ι.range) → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A) → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) B) := by
  first | exact @GlobalTheory.etale_localization_of_cokernel_killed | exact GlobalTheory.etale_localization_of_cokernel_killed | (intros; apply GlobalTheory.etale_localization_of_cokernel_killed <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.etale_quotient_of_etale_punctured' : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] (f : R) [IsLocalRing (R ⧸ Ideal.span {f})], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ (P : Ideal (R ⧸ Ideal.span {f})) [P.IsPrime], P ≠ maximalIdeal (R ⧸ Ideal.span {f}) → Algebra.Etale (Localization.AtPrime P) (TensorProduct (R ⧸ Ideal.span {f}) (Localization.AtPrime P) (A ⧸ (Ideal.span {f}).map (algebraMap R A))) := by
  first | exact @GlobalTheory.etale_quotient_of_etale_punctured | exact GlobalTheory.etale_quotient_of_etale_punctured | (intros; apply GlobalTheory.etale_quotient_of_etale_punctured <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.formallyEtale_away_of_etale_off_maximalIdeal : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g) (TensorProduct R (Localization.Away g) A) := by
  first | exact @GlobalTheory.EtaleAway.formallyEtale_away | exact GlobalTheory.EtaleAway.formallyEtale_away | (intros; apply GlobalTheory.EtaleAway.formallyEtale_away <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.etale_local_ring_of_localization : ∀ (R A E : Type) [CommRing R] [CommRing A] [CommRing E] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime] [Algebra (Localization.AtPrime q) E] [Algebra.Etale (Localization.AtPrime q) E] [Algebra R E] [IsScalarTower R (Localization.AtPrime q) E] (P : Ideal E) [P.IsPrime], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  first | exact @GlobalTheory.essEtale_atPrime_of_etale_over_atPrime | exact GlobalTheory.essEtale_atPrime_of_etale_over_atPrime | (intros; apply GlobalTheory.essEtale_atPrime_of_etale_over_atPrime <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.PicLoc

open Algebra in
theorem finite_maximalSpectrum_of_field (B : Type) [CommRing B] (S : Submonoid B) (K : Type)
    [Field K] [Algebra B K] [IsLocalization S K] (A' : Type) [CommRing A'] [Algebra B A']
    [FormallyUnramified B A'] [FiniteType B A'] (R : Type) [CommRing R] [Algebra A' R]
    [IsLocalization (algebraMapSubmonoid A' S) R] [Algebra B R] [IsScalarTower B A' R] :
    Finite (MaximalSpectrum R) := by
  letI : Algebra K R := localizationAlgebra S A'
  haveI : IsScalarTower B K R := isScalarTower_localizationAlgebra S A'
  haveI : FormallyEtale A' R := FormallyEtale.of_isLocalization (algebraMapSubmonoid A' S)
  haveI : FormallyUnramified B R := FormallyUnramified.comp B A' R
  haveI : FormallyUnramified K R := FormallyUnramified.of_restrictScalars B K R
  haveI : EssFiniteType A' R := EssFiniteType.of_isLocalization R (algebraMapSubmonoid A' S)
  haveI : EssFiniteType B R := EssFiniteType.comp B A' R
  haveI : EssFiniteType K R := EssFiniteType.of_comp B K R
  haveI : Module.Finite K R := FormallyUnramified.finite_of_free K R
  haveI : IsArtinianRing R := IsArtinianRing.of_finite K R
  infer_instance

theorem isField_localization (B : Type) [CommRing B] [IsDedekindDomain B] (f : B)
    (h0 : (0 : B) ∉ (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f) :
    IsField (Localization ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)) := by
  set S : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hS
  haveI : IsDomain (Localization S) :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors h0)

  have hbot : ∀ Q : Ideal (Localization S), Q.IsPrime → Q = ⊥ := by
    intro Q hQ
    set p := Q.comap (algebraMap B (Localization S)) with hp
    haveI : p.IsPrime := Ideal.comap_isPrime _ Q
    have hdisj : ∀ s ∈ S, s ∉ p := by
      intro s hs hsp
      exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hsp
        (IsLocalization.map_units (Localization S) ⟨s, hs⟩))
    have hp0 : p = ⊥ := by
      by_contra hne
      have hmax : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
      have hf : f ∉ p := fun h => hdisj f (Submonoid.mem_sup_right (Submonoid.mem_powers f)) h
      have htop : p ⊔ Ideal.span {f} = ⊤ := by
        refine hmax.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hf ?_)
        rw [h]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : B) ∈ p ⊔ Ideal.span {f})
      have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {f}) a) := by
        have hb0 : Ideal.Quotient.mk (Ideal.span {f}) b = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hb
        have : Ideal.Quotient.mk (Ideal.span {f}) a = 1 := by
          rw [← map_one (Ideal.Quotient.mk (Ideal.span {f})), ← hab, map_add (f := _), hb0, add_zero]
        rw [this]; exact isUnit_one
      exact hdisj a (Submonoid.mem_sup_left hunit) ha
    rw [← IsLocalization.map_under S (Localization S) Q]
    change Ideal.map _ p = ⊥
    rw [hp0, Ideal.map_bot]
  haveI : Ring.KrullDimLE 0 (Localization S) := by
    rw [Ring.krullDimLE_zero_iff]
    intro I hI
    obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal (Localization S)) bot_ne_top
    rw [hbot I hI, ← hbot m hm.isPrime]
    exact hm
  exact Ring.KrullDimLE.isField_of_isDomain

end GlobalTheory.PicLoc

namespace GlobalTheory.PicLoc

theorem subsingleton_pic_localization : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], Subsingleton (CommRing.Pic (Localization (Algebra.algebraMapSubmonoid A' ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)))) := by
  intro B _ _ f A' _ _ _
  set S : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hS
  suffices Finite (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid A' S))) from
    inferInstance
  by_cases h0 : (0 : B) ∈ S
  · have h0' : (0 : A') ∈ Algebra.algebraMapSubmonoid A' S :=
      Submonoid.mem_map.2 ⟨0, h0, map_zero _⟩
    letI := IsLocalization.uniqueOfZeroMem
      (S := Localization (Algebra.algebraMapSubmonoid A' S)) h0'
    haveI : IsEmpty (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid A' S))) :=
      ⟨fun m => m.isMaximal.ne_top (by
        rw [Ideal.eq_top_iff_one, Subsingleton.elim (1 : Localization _) 0]
        exact m.asIdeal.zero_mem)⟩
    infer_instance
  · letI : Field (Localization S) := (isField_localization B f h0).toField
    exact finite_maximalSpectrum_of_field B S (Localization S) A'
      (Localization (Algebra.algebraMapSubmonoid A' S))

end GlobalTheory.PicLoc
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_etale_away_of_isEtaleAt : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C]
    (M : Submonoid R),
    (∀ (Q : Ideal C) [Q.IsPrime], (∀ m ∈ M, algebraMap R C m ∉ Q) → Algebra.IsEtaleAt R Q) →
    ∃ m ∈ M, Algebra.Etale R (Localization.Away (algebraMap R C m)) := by
  first | (exact @GlobalTheory.etale_away_of_isEtaleAt_off_submonoid) | (exact GlobalTheory.etale_away_of_isEtaleAt_off_submonoid) | (intros; apply GlobalTheory.etale_away_of_isEtaleAt_off_submonoid <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.standardEtale_localization_away_quotient_span : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∃ (f g : MvPolynomial (Option (Fin n)) A), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) ∧ (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : Option (Fin n) → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv none (MvPolynomial.map ψ f)) ≠ 0) ∧ Nonempty (B ≃ₐ[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)) := by
  first | exact @GlobalTheory.standardEtale_mvPolynomial_hypersurface | exact GlobalTheory.standardEtale_mvPolynomial_hypersurface | (intros; apply GlobalTheory.standardEtale_mvPolynomial_hypersurface <;> assumption)
end

section


theorem _root_.GlobalTheory.T.injective_cotangentComplexBaseChange_of_forms_extend' : ∀ (A P R K : Type) [CommRing A] [CommRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], (∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i) → Function.Injective (KaehlerDifferential.cotangentComplexBaseChange A R P K) := by
  first | exact @GlobalTheory.injective_cotangentComplexBaseChange_of_forms_extend | exact GlobalTheory.injective_cotangentComplexBaseChange_of_forms_extend | (intros; apply GlobalTheory.injective_cotangentComplexBaseChange_of_forms_extend <;> assumption)
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory
namespace FactorAway

theorem factor_away : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra.FinitePresentation R A] (p : Ideal B) [p.IsPrime]
    (φ : A →ₐ[R] Localization.AtPrime p), ∃ (g : B) (hg : g ∉ p)
      (ψ : A →ₐ[R] Localization.Away g), ∀ a, Localization.awayLift
        (algebraMap B (Localization.AtPrime p)) g
        (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) (ψ a) = φ a := by
  intro R A B _ _ _ _ _ _ p _ φ
  let φ' : B ⊗[R] A →ₐ[B] Localization.AtPrime p :=
    Algebra.TensorProduct.lift (Algebra.ofId B _) φ (fun _ _ => Commute.all _ _)
  obtain ⟨g, hg, s, ι, hι⟩ := SpreadOut.spread_out B (B ⊗[R] A) p φ'
  refine ⟨g, hg, (s.restrictScalars R).comp Algebra.TensorProduct.includeRight, fun a => ?_⟩
  have hext : (Localization.awayLift (algebraMap B (Localization.AtPrime p)) g
      (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl))) =
      (ι : Localization.Away g →+* Localization.AtPrime p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext b
    simp [Localization.awayLift]
  have h1 := congrArg (fun h => h ((1 : B) ⊗ₜ[R] a)) hι
  simp only [AlgHom.comp_apply, φ', Algebra.TensorProduct.lift_tmul, map_one, one_mul] at h1
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
  rw [hext]
  exact h1

end FactorAway
end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.finiteType_invariants_finite_group_and_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra.FiniteType R C'] (G : Type) [Group G] [Finite G] (act : G →* (C' ≃ₐ[R] C')) (C : Subalgebra R C'), (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' := by
  first | exact @GlobalTheory.finiteType_invariants_and_finite | exact GlobalTheory.finiteType_invariants_and_finite | (intros; apply GlobalTheory.finiteType_invariants_and_finite <;> assumption)
end
