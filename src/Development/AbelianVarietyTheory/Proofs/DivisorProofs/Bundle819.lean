module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle797
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianNormalLocalApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle802
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle064
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle324
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle732
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle202
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle790
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle754

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_vf_of_frame {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hF : HasFrame F) (h0 : CohomZeroIsConstants F) (l : Glob1 F →ₗ[R] R) :
    ∃ δ : ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T,
      (∀ ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ T' (p1 F φ ω) = mp F φ (δ T ω)) ∧
      ∀ (w : Glob1 F) T, δ T (w.1 T) = algebraMap R (F.obj T) (l w) := by
  apply GlobalTheory.AbCoh.exists_vectorField_of_functional <;> assumption

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem derivClass_eq : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F) (y' : Fin n' → GlobalTheory.CatCoh.H1 F) (w' : Fin n' → Glob1 F), DRel F x y w → DRel F x y' w' → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = ∑ k, l (w' k) • y' k := by
  intro R _ C _ F hF h0 x n n' y w y' w' hd hd' l
  obtain ⟨δ, hnat, hδ⟩ := exists_vf_of_frame F hF h0 l
  obtain ⟨f, g, ω, rfl, hg, hf⟩ := hd
  obtain ⟨f', g', ω', hx, hg', hf'⟩ := hd'
  obtain ⟨b, hb⟩ := H1.mk_eq_mk.1 hx
  obtain rfl : y = fun k ↦ H1.mk F (g k) := funext fun k ↦ (hg k).symm
  obtain rfl : y' = fun k ↦ H1.mk F (g' k) := funext fun k ↦ (hg' k).symm
  have e1 : ∑ k, l (w k) • H1.mk F (g k) = H1.mk F (∑ k, l (w k) • g k) := by simp [map_sum, map_smul]
  have e2 : ∑ k, l (w' k) • H1.mk F (g' k) = H1.mk F (∑ k, l (w' k) • g' k) := by simp [map_sum, map_smul]
  rw [e1, e2, H1.mk_eq_mk]
  refine ⟨fun T ↦ δ T (ω' T - ω T - D R _ (b T)), ?_⟩
  funext T T' φ
  have hbφ : d0 F b T T' φ = f'.1 T T' φ - f.1 T T' φ := congrFun (congrFun (congrFun hb T) T') φ
  have key : D R _ (f'.1 T T' φ) - D R _ (f.1 T T' φ) = D R _ (b T') - p1 F φ (D R _ (b T)) := by
    rw [← map_sub, ← hbφ, amitsur_d0_apply, map_sub, p1_D]
  rw [hf φ, hf' φ] at key
  have e := congrArg (δ T') key

  simp only [map_sub, map_add (f := _), map_sum, LinearMap.map_smul, hnat, hδ, smul_eq_mul] at e
  simp only [amitsur_d0_apply, map_sub, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.sub_apply, Pi.smul_apply]
  simp only [Algebra.smul_def]
  simp only [mul_comm (algebraMap R _ _)] at e ⊢
  linear_combination e

end GlobalTheory.AbCoh
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginNoeth

theorem mem_originIdeal_iff {T : Type} [CommRing T] [IsLocalRing T] (f : Polynomial T) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal T ↔ f.coeff 0 ∈ maximalIdeal T := by
  apply GlobalTheory.VertUnitsNoeth.mem_originIdeal_iff' <;> assumption

theorem comap_originIdeal (A T : Type) [CommRing A] [IsLocalRing A] [CommRing T] [IsLocalRing T]
    (i : A →+* T) [IsLocalHom i] :
    (GlobalTheory.KeyOriginCut.originIdeal T).comap (Polynomial.mapRingHom i) = GlobalTheory.KeyOriginCut.originIdeal A := by
  ext f
  rw [Ideal.mem_comap, mem_originIdeal_iff, mem_originIdeal_iff, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_map_iff]

theorem isIntegrallyClosed_of_absIntClosed (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) : IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx0
  obtain ⟨p, hpm, hpx⟩ := hx0
  suffices H : ∀ n : ℕ, ∀ p : Polynomial T, p.Monic → p.natDegree = n → Polynomial.eval₂ (algebraMap T (FractionRing T)) x p = 0 →
      ∃ y, algebraMap T (FractionRing T) y = x from H _ p hpm rfl hpx
  intro n
  induction n with
  | zero =>
    intro p hp hd hx
    have h1 := Polynomial.eq_one_of_monic_natDegree_zero hp hd
    subst h1
    simp at hx
  | succ n ih =>
    intro p hp hd hx
    obtain ⟨r, hr⟩ := hT p hp (by omega)
    have hroot : p.IsRoot r := hr
    have hdec := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
    set p' := p /ₘ (Polynomial.X - Polynomial.C r)
    have hp' : p'.Monic := (Polynomial.monic_X_sub_C r).of_mul_monic_left (by rw [hdec]; exact hp)
    have hd' : p'.natDegree = n := by
      have := congrArg Polynomial.natDegree hdec
      rw [(Polynomial.monic_X_sub_C r).natDegree_mul hp', Polynomial.natDegree_X_sub_C] at this
      omega
    rw [← hdec, Polynomial.eval₂_mul] at hx
    rcases mul_eq_zero.mp hx with h | h
    · refine ⟨r, ?_⟩
      simp at h
      exact (sub_eq_zero.mp h).symm
    · exact ih p' hp' hd' h

theorem norm_finiteType {T : Type} [CommRing T] [IsDomain T] [IsIntegrallyClosed T] (S : Finset T) :
    Algebra.FiniteType ℤ (GlobalTheory.NormalApprox.norm S) := by
  haveI := GlobalTheory.finite_integralClosure_of_essFiniteType_int (GlobalTheory.NormalApprox.gen S)
  haveI : Algebra.FiniteType ℤ
      (integralClosure (GlobalTheory.NormalApprox.gen S) (FractionRing (GlobalTheory.NormalApprox.gen S))) :=
    Algebra.FiniteType.trans (S := GlobalTheory.NormalApprox.gen S) inferInstance inferInstance
  exact Algebra.FiniteType.equiv this
    (AlgEquiv.ofRingEquiv (f := (GlobalTheory.NormalApprox.normEquiv S).symm) (fun n => by simp))

theorem loc_essFiniteType {T : Type} [CommRing T] [IsDomain T] [IsIntegrallyClosed T] (S : Finset T) :
    Algebra.EssFiniteType ℤ (GlobalTheory.NormalApprox.loc S) := by
  haveI := norm_finiteType S
  haveI := GlobalTheory.NormalApprox.loc_isLocalization S
  haveI : Algebra.EssFiniteType (GlobalTheory.NormalApprox.norm S) (GlobalTheory.NormalApprox.loc S) :=
    Algebra.EssFiniteType.of_isLocalization _ (GlobalTheory.NormalApprox.unitsIn S)
  exact Algebra.EssFiniteType.comp ℤ (GlobalTheory.NormalApprox.norm S) (GlobalTheory.NormalApprox.loc S)

theorem exists_noetherian_model : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E]
      [IsScalarTower T (Polynomial T) E] [Algebra.Etale (Polynomial T) E]
      (Q : Ideal E) [Q.IsPrime],
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (j : Localization.AtPrime Q →+* O),
      j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O →
    ∀ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j →
    ∀ (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (_ : IsIntegrallyClosed A) (_ : Algebra.EssFiniteType ℤ A) (i : A →+* T), Function.Injective i ∧ IsLocalHom i ∧ IsUnit (q : A) ∧
      ∃ (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial A) EA) (_ : Algebra A EA)
        (_ : IsScalarTower A (Polynomial A) EA) (_ : Algebra.Etale (Polynomial A) EA)
        (QA : Ideal EA) (_ : QA.IsPrime),
        QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
      ∃ (jA : Localization.AtPrime QA →+* O),
        jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
          (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
      ∃ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA ∧
      ∃ (DA : Type) (_ : CommRing DA) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)
        (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA ∧
        ∀ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA →
          ∃ σ₁ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  intro T O _ _ _ _ _ _ _ _ hT q hq hqT E _ _ _ _ _ Q _ hQ j hj ψ hψ D₁ _ _ act₁ htor
  have hTic : IsIntegrallyClosed T := isIntegrallyClosed_of_absIntClosed T hT
  let 𝒜 : Finset T → Subring T := GlobalTheory.NormalApprox.loc
  have hmono : Monotone 𝒜 := GlobalTheory.NormalApprox.loc_mono
  have hcov : ∀ (S : Finset T), ∀ x ∈ S, x ∈ 𝒜 S := fun S x hx => GlobalTheory.NormalApprox.mem_loc_of_mem S hx
  have hprop : ∀ S, IsNoetherianRing (𝒜 S) ∧ IsIntegrallyClosed (𝒜 S) ∧ IsLocalRing (𝒜 S) ∧
      (∀ x : 𝒜 S, IsUnit (x : T) → IsUnit x) ∧ Algebra.EssFiniteType ℤ (𝒜 S) := by
    intro S
    haveI := GlobalTheory.NormalApprox.loc_isLocalization S
    haveI := GlobalTheory.NormalApprox.norm_isIntegrallyClosed S
    exact ⟨IsLocalization.isNoetherianRing (GlobalTheory.NormalApprox.unitsIn S) _ (GlobalTheory.NormalApprox.norm_isNoetherianRing S),
      isIntegrallyClosed_of_isLocalization (GlobalTheory.NormalApprox.loc S) (GlobalTheory.NormalApprox.unitsIn S)
        (GlobalTheory.NormalApprox.unitsIn_le S),
      GlobalTheory.NormalApprox.loc_isLocalRing S, GlobalTheory.NormalApprox.isUnit_of_isUnit_coe S, loc_essFiniteType S⟩
  obtain ⟨S, EA, _, _, _, _, _, e, he, β, hβ, D, _, _, actA, htorA, hlast⟩ :=
    GlobalTheory.T.exists_torsor_descent_directedUnion_subring T (Finset T) 𝒜 hmono (fun x => ⟨{x}, hcov {x} x (Finset.mem_singleton_self x)⟩) q hq E Q D₁ act₁ htor
  obtain ⟨hN, hIC, hL, hU, hEF⟩ := hprop S
  have hloc : IsLocalHom (𝒜 S).subtype := ⟨fun a ha => hU a ha⟩
  have hqA : IsUnit (q : 𝒜 S) := hU _ (by simpa using hqT)
  have horig : (Q.comap e).comap (algebraMap (Polynomial (𝒜 S)) EA) = GlobalTheory.KeyOriginCut.originIdeal (𝒜 S) := by
    rw [Ideal.comap_comap, he, ← Ideal.comap_comap, hQ]
    exact comap_originIdeal (𝒜 S) T (𝒜 S).subtype
  let jA : Localization.AtPrime (Q.comap e) →+* O := j.comp (Localization.localRingHom (Q.comap e) Q e rfl)
  have hjA : jA.comp (algebraMap (Polynomial (𝒜 S)) (Localization.AtPrime (Q.comap e))) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom (𝒜 S).subtype) := by
    refine RingHom.ext fun x => ?_
    change j (Localization.localRingHom (Q.comap e) Q e rfl
      (algebraMap (Polynomial (𝒜 S)) (Localization.AtPrime (Q.comap e)) x)) = _
    rw [IsScalarTower.algebraMap_apply (Polynomial (𝒜 S)) EA (Localization.AtPrime (Q.comap e)),
      Localization.localRingHom_to_map, ← RingHom.comp_apply e, he, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply, ← RingHom.comp_apply j, hj]
    rfl
  refine ⟨𝒜 S, inferInstance, inferInstance, hL, hN, hIC, hEF, (𝒜 S).subtype, Subtype.val_injective, hloc, hqA,
    EA, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q.comap e, inferInstance, horig,
    jA, hjA, ψ.comp β, ?_, D, inferInstance, inferInstance, actA, htorA, fun σ hσ => hlast _ ψ σ hσ⟩
  rw [RingHom.comp_assoc, hβ, ← RingHom.comp_assoc, hψ]
  rfl

end GlobalTheory.KeyOriginNoeth
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.OrderUnits

theorem prime_not_mem_sq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (w : HeightOneSpectrum (𝓞 E)) (hv : (p : 𝓞 E) ∈ w.asIdeal) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  apply GlobalTheory.LamTie.ExpCond.not_mem_sq_of_not_dvd_discr <;> assumption

theorem pow_first_order {R : Type} [CommRing R] (t : R) (i : ℕ) : ∃ r, (1 + t) ^ i = 1 + i * t + t ^ 2 * r := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨r + i + t * r, by rw [pow_succ, hr]; push_cast; ring⟩

theorem geom_first_order {R : Type} [CommRing R] (t : R) (n : ℕ) :
    ∃ r, ∑ i ∈ Finset.range n, (1 + t) ^ i = n + (n.choose 2 : ℕ) * t + t ^ 2 * r := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨s, hs⟩ := pow_first_order t n
    refine ⟨r + s, ?_⟩
    rw [Finset.sum_range_succ, hr, hs, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    push_cast; ring

theorem root_of_unity_eq_one {R : Type} [CommRing R] [IsDomain R] {P : Ideal R} (hP : P ≠ ⊤) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hlP : (l : R) ∈ P) (hlP2 : (l : R) ∉ P ^ 2) {ζ : R} (hζ : IsOfFinOrder ζ) (h1 : ζ - 1 ∈ P) : ζ = 1 := by
  by_contra hne
  have hn : orderOf ζ ≠ 1 := fun h => hne (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hp, m, hm⟩ := Nat.exists_prime_and_dvd hn
  have hpos := hζ.orderOf_pos
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp [hm] at hpos)
  have hη1 : ζ ^ m ≠ 1 := pow_ne_one_of_lt_orderOf hm0.ne' (by rw [hm]; nlinarith [hp.two_le])
  have hηp : (ζ ^ m) ^ p = 1 := by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  have ht : ζ ^ m - 1 ∈ P := by
    obtain ⟨s, hs⟩ := sub_one_dvd_pow_sub_one ζ m
    rw [hs]; exact P.mul_mem_right _ h1
  have hsum : ∑ i ∈ Finset.range p, (ζ ^ m) ^ i = 0 := by
    have := mul_geom_sum (ζ ^ m) p
    rw [hηp, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hη1)
  obtain ⟨r, hr⟩ := geom_first_order (ζ ^ m - 1) p
  rw [add_sub_cancel, hsum] at hr
  set t := ζ ^ m - 1
  have hpe : (p : R) = -((p.choose 2 : ℕ) * t) - t ^ 2 * r := by linear_combination -hr
  have hpP : (p : R) ∈ P := by
    rw [hpe]
    exact sub_mem (neg_mem (P.mul_mem_left _ ht)) (P.mul_mem_right _ (P.pow_mem_of_mem ht 2 two_pos))
  have hpl : p = l := by
    by_contra h
    have hc : IsCoprime (p : R) (l : R) := Nat.Coprime.cast ((Nat.coprime_primes hp hl).2 h)
    obtain ⟨a, b, hab⟩ := hc
    exact hP ((Ideal.eq_top_iff_one P).2 (hab ▸ add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hlP)))
  subst hpl
  obtain ⟨k, hk⟩ := hp.dvd_choose_self two_ne_zero (lt_of_le_of_ne hp.two_le (Ne.symm hl2))
  apply hlP2
  rw [hpe, hk]
  refine sub_mem (neg_mem ?_) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ht 2))
  rw [sq]
  push_cast
  exact Ideal.mul_mem_mul (P.mul_mem_right _ hlP) ht

theorem orderC_units (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (hc : 𝔣 ∣ c)
    (x : E) (hx0 : x ≠ 0) (hx : x ∈ orderC c) (hx' : x⁻¹ ∈ orderC c) : ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u := by
  obtain ⟨h0, h1, h⟩ := h𝔣
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal 𝔣 h1
  have hM0 : M ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hle))
  obtain ⟨⟨P, -, -, hP, -⟩, -, l, hl, hl2, hlv, hd, -⟩ := h ⟨M, hM.isPrime, hM0⟩ (Ideal.dvd_iff_le.2 hle)
  have hP' : P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) = M := hP
  have hlP : (l : 𝓞 E) ∈ P.asIdeal := by
    have : (l : OF E) ∈ P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) := by rw [hP']; exact hlv
    simpa using this
  have hcP : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.2 (hP' ▸ (Ideal.le_of_dvd hc).trans hle)
  obtain ⟨a, b, hb, hab⟩ := mem_orderC.1 hx
  obtain ⟨a', b', -, hab'⟩ := mem_orderC.1 hx'
  have e1 : x = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by rw [hab, map_add (f := _)]; rfl
  have e2 : x⁻¹ = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a' + b') := by rw [hab', map_add (f := _)]; rfl
  have hu : (algebraMap (OF E) (𝓞 E) a + b) * (algebraMap (OF E) (𝓞 E) a' + b') = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_mul, ← e1, ← e2, mul_inv_cancel₀ hx0, map_one]
  let u : (𝓞 E)ˣ := Units.mkOfMulEqOne _ _ hu
  have huv : (u : 𝓞 E) = algebraMap (OF E) (𝓞 E) a + b := rfl
  have hbc : IsCMField.ringOfIntegersComplexConj E b ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    have : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤
        (Ideal.map (algebraMap (OF E) (𝓞 E)) c).comap (IsCMField.ringOfIntegersComplexConj E) := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgEquiv.commutes]
      exact Ideal.mem_map_of_mem _ hy
    exact this hb
  have hcu : ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E) =
      algebraMap (OF E) (𝓞 E) a + IsCMField.ringOfIntegersComplexConj E b := by
    have : ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E) = IsCMField.ringOfIntegersComplexConj E u := rfl
    rw [this, huv, map_add (f := _), AlgEquiv.commutes]
  let ζ : (𝓞 E)ˣ := u * (IsCMField.unitsComplexConj E u)⁻¹
  have hfin : IsOfFinOrder ζ := (IsCMField.unitsMulComplexConjInv E u).2
  have hfin' : IsOfFinOrder (ζ : 𝓞 E) := (Units.coeHom (𝓞 E)).isOfFinOrder hfin
  have hζ : (ζ : 𝓞 E) - 1 ∈ P.asIdeal := by
    have : (ζ : 𝓞 E) - 1 = (b - IsCMField.ringOfIntegersComplexConj E b) * ↑(IsCMField.unitsComplexConj E u)⁻¹ := by
      have h3 := (IsCMField.unitsComplexConj E u).mul_inv
      rw [hcu] at h3
      simp only [ζ, Units.val_mul, huv]
      linear_combination h3
    rw [this]
    exact P.asIdeal.mul_mem_right _ (hcP (sub_mem hb hbc))
  have hone : ζ = 1 := Units.ext (root_of_unity_eq_one P.isPrime.ne_top hl hl2 hlP (prime_not_mem_sq hl hd P hlP) hfin' hζ)
  have hreal := (IsCMField.unitsComplexConj_eq_self_iff E u).1 (mul_inv_eq_one.1 hone).symm
  obtain ⟨v, hv⟩ := (IsCMField.mem_realUnits_iff E u).1 hreal
  refine ⟨v, ?_⟩
  rw [e1, ← huv, ← hv]
  rfl

end GlobalTheory.CMVal.OrderUnits
end

section

noncomputable section
open NumberField MeasureTheory

namespace GlobalTheory.HeckeStrip

theorem completed_pSeries_entire_bounded : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  intro K _ _ _ I _ φ hφ n hn M F hM hper hinv
  haveI : Nonempty I := ⟨hn.choose⟩
  obtain ⟨p, hpm, hp0, hpsum, R, hpR⟩ := GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates K I φ hφ
  obtain ⟨⟨C, hC⟩, hsumm, hge⟩ := GlobalTheory.T.periodic_bounded_gaussian_summable_cmType K I φ hφ M F hM hper
  obtain ⟨a, κ, hasumm, ⟨δ, hδ, hδa⟩, hfe⟩ := GlobalTheory.T.heckeThetaKernel_poisson_summation K I φ hφ n M F hM hper
  have hp1 : ∀ y, p y ≤ 1 := fun y => by
    have h := le_hasSum (hpsum y) 1 (fun u _ => hp0 _)
    have h0 : GlobalTheory.HeckeTheta.ulog φ (1 : (𝓞 K)ˣ) = 0 := by
      funext i; simp [GlobalTheory.HeckeTheta.ulog]
    simpa [h0] using h
  have hpB : ∀ y, |p y| ≤ 1 := fun y => abs_le.2 ⟨by linarith [hp0 y], hp1 y⟩
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hℓ : Measurable (fun y : I → ℝ => ∑ i, y i) := by fun_prop
  have hS0 : ∀ᵐ y ∂(volume.restrict S), 0 ≤ ∑ i, y i := ae_restrict_of_forall_mem hSm fun y hy => hy
  obtain ⟨D1m, D1i⟩ := GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace I (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n p 1 R hn hsumm
    ⟨1, one_pos, fun α _ h => hge α h⟩ hpm hpB hpR
  obtain ⟨D2m, D2i⟩ := GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace I (fun v : I → ℂ => v) a n (fun y => p (-y)) 1 R hn hasumm ⟨δ, hδ, hδa⟩
    (hpm.comp measurable_neg) (fun y => hpB _) (fun y hy i j => by
      have := hpR (-y) hy j i
      simp only [Pi.neg_apply] at this
      linarith)
  have A1 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D1m.restrict hS0 D1i
  have A2 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D2m.restrict hS0 D2i
  have hint : ∀ (g : (I → ℝ) → ℂ) (t : ℂ), AEStronglyMeasurable g volume →
      (∀ σ : ℝ, Integrable (fun y => ‖g y‖ * Real.exp (σ * ∑ i, y i)) (volume.restrict S)) →
      Integrable (fun y => g y * Complex.exp (t * ((∑ i, y i : ℝ) : ℂ))) (volume.restrict S) := by
    intro g t hg hgi
    refine (hgi t.re).mono' (hg.restrict.mul (Continuous.aestronglyMeasurable (by fun_prop))) (ae_of_all _ fun y => ?_)
    rw [norm_mul, Complex.norm_exp]
    apply le_of_eq
    congr 2
    simp [Complex.mul_re]
  set f1 : ℂ → ℂ := fun s => ∫ y in S, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf1
  set f2 : ℂ → ℂ := fun s => ∫ y in S, (p (-y) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf2
  have hd1 : Differentiable ℂ f1 := A1.1
  have hd2 : Differentiable ℂ f2 := A2.1
  have hb1 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f1 := A1.2
  have hb2 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f2 := A2.2
  refine ⟨fun s => 2 ^ Fintype.card I * (f1 s + κ * f2 (1 - s)), ?_, ?_, ?_⟩
  · exact (hd1.add ((hd2.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).const_mul κ)).const_mul _
  · intro a' b' hab
    obtain ⟨C1, hC1⟩ := hb1 a' b' hab
    obtain ⟨C2, hC2⟩ := hb2 (1 - b') (1 - a') (by linarith)
    refine ⟨‖(2 : ℂ) ^ Fintype.card I‖ * (C1 + ‖κ‖ * C2), fun s h1 h2 => ?_⟩
    rw [norm_mul]
    gcongr
    refine (norm_add_le _ _).trans (add_le_add (hC1 s h1 h2) ?_)
    rw [norm_mul]
    gcongr
    exact hC2 (1 - s) (by simp; linarith) (by simp; linarith)
  · intro s hs
    rw [GlobalTheory.T.archFactor_mul_pSeries_eq_integral_alt K I φ hφ n hn F C hC hinv p hpm hp0 hpsum s hs,
      GlobalTheory.T.mellin_integral_split_functional_equation I p _ _ κ s hfe (hint _ s D1m D1i) (hint _ (1 - s) D2m D2i)]

end GlobalTheory.HeckeStrip
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal

theorem _root_.GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve : ∀ (l : ℕ), l.Prime → ∀ (r : ℝ) (J : Type) [Fintype J] (u x : J → ℂ), (∀ j, IntAt l (u j)) → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r (x j ^ 12)) → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r ((∑ j, u j * x j) ^ 12) := by
  first | exact @GlobalTheory.LatValSum.valGe_sum_pow_twelve | exact GlobalTheory.LatValSum.valGe_sum_pow_twelve | (intros; apply GlobalTheory.LatValSum.valGe_sum_pow_twelve <;> assumption)
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_borelInvariant_testFunction_frameChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r), ∃ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧ ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ 0 ∧ ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ ⊤ := by
  first | exact @GlobalTheory.FlagQuotHaar.TestFn.exists_invariant_test | exact GlobalTheory.FlagQuotHaar.TestFn.exists_invariant_test | (intros; apply GlobalTheory.FlagQuotHaar.TestFn.exists_invariant_test <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.center_acts_by_scalar_on_eigenforms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (c : (E →+* ℂ) → ℂ → ℂ) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a → ∃ s : ℂ, ∀ φ : GlobalTheory.CuspRep.Sm E a, (∀ τ u, GlobalTheory.CuspRep.cap τ u φ = c τ u • φ) → z φ = s • φ := by
  first | exact @GlobalTheory.CuspRep.Zalg_acts_by_scalar | exact GlobalTheory.CuspRep.Zalg_acts_by_scalar | (intros; apply GlobalTheory.CuspRep.Zalg_acts_by_scalar <;> assumption)
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.eop_preserves_left_unipotent_invariance : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (f : Sm E a), (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a) (x : BlockIx a r → Ad E) (g : GA E a), (Eop τ i j f).1 (unip x * g) = (Eop τ i j f).1 g := by
  first | exact @GlobalTheory.CuspRep.UnipInv.Eop_unip_left | exact GlobalTheory.CuspRep.UnipInv.Eop_unip_left | (intros; apply GlobalTheory.CuspRep.UnipInv.Eop_unip_left <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

theorem _root_.GlobalTheory.T.finite_closure_theta_ratios_of_isCl' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (J : Type) (t : J → Ω), M.IsCl t → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)})) Ω := by
  first | exact @GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl | exact GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl | (intros; apply GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl <;> assumption)
end
