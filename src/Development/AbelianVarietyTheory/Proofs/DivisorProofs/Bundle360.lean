module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle293
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228

@[expose] public section

section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits


open GlobalTheory.LocAcyc in
open CategoryTheory in
theorem divConstAll_of_divConstLocal : DivConstLocal → DivConstAll := by
  intro hL T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH
  set p : Ideal T := P.comap (C : T →+* T[X]) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let T' := Localization.AtPrime p
  have hle : p.primeCompl ≤ nonZeroDivisors T := p.primeCompl_le_nonZeroDivisors
  have hAIC' : AbsIntClosed T' :=
    ((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl
      (fun h => h (zero_mem p))).2
  have hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a) := fun a => by
    rw [IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s) := by
    intro s
    have hs : C (s : T) ∈ P.primeCompl := s.2
    have hu := (IsLocalization.map_units (Localization.AtPrime P)
      (⟨C (s : T), hs⟩ : P.primeCompl)).map φ
    rw [← RingHom.comp_apply, hφ] at hu
    rwa [hTO]
  letI : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra
  haveI : IsScalarTower T T' O :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  letI : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra
  haveI : IsScalarTower T' T'[X] O :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)
      rw [Polynomial.algebraMap_eq, eval₂_C])
  letI : Algebra T[X] T'[X] := Polynomial.algebra T T'
  haveI : IsLocalization (Submonoid.map C p.primeCompl) T'[X] :=
    Polynomial.isLocalization p.primeCompl T'
  have hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'
  haveI hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj
  have hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P :=
    IsLocalization.under_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj
  have hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a) := fun a => by
    change _ = (C a).map (algebraMap T T')
    rw [Polynomial.map_C]
  have hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T' := by
    rw [← IsLocalization.map_under p.primeCompl T' (P'.comap C),
      ← IsLocalization.map_under p.primeCompl T' (maximalIdeal T'),
      IsLocalization.AtPrime.under_maximalIdeal T' p]
    congr 1
    ext a
    change C (algebraMap T T' a) ∈ P' ↔ C a ∈ P
    rw [hCcomm, ← Ideal.mem_comap, hcomapP']
  haveI : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'
    have hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomapP']
    unfold IsLocalization.AtPrime at this ⊢
    rw [hc] at this
    exact this
  let e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  let φ' : Localization.AtPrime P' →+* O := φ.comp e.symm.toRingEquiv.toRingHom
  have hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _
      rw [Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _
      rw [Polynomial.map_X, eval₂_X]
  have hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O := by
    refine IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]
    refine RingHom.ext fun f => ?_
    change φ (e.symm (algebraMap T[X] _ f)) = _
    rw [AlgEquiv.commutes, ← RingHom.comp_apply, hφ]
  have hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hSH
    refine ⟨h1, h2, ?_, ?_⟩
    · refine ⟨fun a ha => ?_⟩
      change IsUnit (φ (e.symm a)) at ha
      have h5 : IsUnit (e.symm a) := h3.map_nonunit _ ha
      simpa using h5.map e
    · haveI : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢
      rw [CommRingCat.ofHom_comp]
      haveI : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) :=
        inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)
      exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4
  have key : DivConst T' O := hL T' O hAIC' P' φ' hφ' hSH' hmax trivial

  have hinj : Function.Injective (algebraMap T T') := IsLocalization.injective T' hle
  intro b c s hs hbc
  have hs' : algebraMap T T' s ≠ 0 := fun h => hs (hinj (by rw [h, map_zero]))
  rw [IsScalarTower.algebraMap_apply T T' O] at hbc
  obtain ⟨a', w, hb⟩ := key b c _ hs' hbc
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a'
  obtain ⟨v, hv⟩ := hunit u
  refine ⟨a, v⁻¹ * w, ?_⟩
  rw [hb, Units.val_mul, ← mul_assoc]
  congr 1
  rw [Units.eq_mul_inv_iff_mul_eq, hv, IsScalarTower.algebraMap_apply T T' O a,
    IsScalarTower.algebraMap_apply T T' O u, ← map_mul, IsLocalization.mk'_spec]

end GlobalTheory.VertUnits
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem divConstClosedPts_of_divConstOrigin :
    GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  intro hKO
  unfold GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith at hKO
  unfold GlobalTheory.VertUnits.DivConstClosedPts GlobalTheory.VertUnits.DivConstWith
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne
  have hne' : P ≠ (maximalIdeal T).map (C : T →+* T[X]) := hne
  haveI hac : IsAlgClosed (ResidueField T) :=
    (GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩).2.1
  obtain ⟨c, hc⟩ := GlobalTheory.LocAcyc.Translate.exists_X_sub_C_mem T P hPm hne'
  let τ : T[X] ≃ₐ[T] T[X] := algEquivAevalXAddC (-c)
  have hτX : τ X = X - C c := by simp [τ, sub_eq_add_neg]
  have hτC : ∀ a : T, τ (C a) = C a := fun a => τ.commutes a
  let P' : Ideal T[X] := P.comap (τ : T[X] →+* T[X])
  haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
  have hP'C : P'.comap (C : T →+* T[X]) = maximalIdeal T := by
    rw [← hPm]; ext a
    simp only [Ideal.mem_comap, P']
    rw [show ((τ : T[X] →+* T[X]) (C a)) = C a from hτC a]
  have hXP' : (X : T[X]) ∈ P' := by
    simp only [P', Ideal.mem_comap]
    rw [show ((τ : T[X] →+* T[X]) X) = X - C c from hτX]; exact hc
  have hP' : P' = (maximalIdeal T).map (C : T →+* T[X]) ⊔ Ideal.span {X} := by
    apply le_antisymm
    · intro p hp
      have hd : p - C (p.coeff 0) ∈ Ideal.span {(X : T[X])} := Ideal.mem_span_singleton.2 X_dvd_sub_C
      have hc0 : C (p.coeff 0) ∈ P' := by
        have h1 : p - C (p.coeff 0) ∈ P' := by
          obtain ⟨u, hu⟩ := (X_dvd_sub_C : X ∣ p - C (p.coeff 0))
          rw [hu]; exact P'.mul_mem_right _ hXP'
        have := P'.sub_mem hp h1
        simpa using this
      have hc0' : p.coeff 0 ∈ maximalIdeal T := by rw [← hP'C]; exact hc0
      have : p = C (p.coeff 0) + (p - C (p.coeff 0)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc0')) (Ideal.mem_sup_right hd)
    · refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, hP'C]
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hXP'

  let f' : T[X] →+* O := (algebraMap T[X] O).comp (τ : T[X] →+* T[X])
  let alg' : Algebra T[X] O := f'.toAlgebra
  have tower' : @IsScalarTower T T[X] O _ alg'.toSMul _ := by
    refine @IsScalarTower.of_algebraMap_eq T T[X] O _ _ _ _ alg' _ ?_
    intro x
    change algebraMap T O x = f' (algebraMap T T[X] x)
    simp only [f', RingHom.comp_apply]
    rw [show (τ : T[X] →+* T[X]) (algebraMap T T[X] x) = algebraMap T T[X] x from τ.commutes x,
      ← IsScalarTower.algebraMap_apply]

  have hmap : P'.primeCompl.map (τ : T[X] ≃+* T[X]).toMonoidHom = P.primeCompl := by
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨(τ : T[X] ≃+* T[X]).symm x, ?_, by simp⟩
      change (τ : T[X] →+* T[X]) ((τ : T[X] ≃+* T[X]).symm x) ∉ P
      have hx' : x ∉ P := hx
      convert hx' using 2
      exact (τ : T[X] ≃+* T[X]).apply_symm_apply x
  let Lq : Localization.AtPrime P' ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv _ _ (τ : T[X] ≃+* T[X]) hmap
  let φ' : Localization.AtPrime P' →+* O := φ.comp (Lq : Localization.AtPrime P' →+* Localization.AtPrime P)
  have hφ' : φ'.comp (algebraMap T[X] (Localization.AtPrime P')) = f' := by
    refine RingHom.ext fun x => ?_
    simp only [φ', f', RingHom.comp_apply]
    rw [show (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) (algebraMap T[X] _ x)
        = algebraMap T[X] (Localization.AtPrime P) ((τ : T[X] ≃+* T[X]) x) from
      IsLocalization.ringEquivOfRingEquiv_eq _ x]
    rw [← RingHom.comp_apply φ, hφ]
    rfl
  have hsh' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hsh
    refine ⟨h1, h2, ?_, ?_⟩
    · haveI := h3
      haveI : IsLocalHom (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) :=
        ⟨fun a ha => by simpa using ha.map (Lq.symm : Localization.AtPrime P →+* Localization.AtPrime P')⟩
      exact RingHom.isLocalHom_comp _ _
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      have h5 := CategoryTheory.MorphismProperty.RespectsIso.precomp
        (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
        Lq.toCommRingCatIso.hom (CommRingCat.ofHom φ) h4
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
      convert h5 using 1
      rfl
  exact @hKO T O _ _ _ _ _ _ alg' tower' hT P' hP'p φ' hφ' hsh' hP'C hP'

end GlobalTheory.VertUnits
end

section

open CategoryTheory Limits
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocAcyc

def zmodTensorAct (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type)
    [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)) :
    Multiplicative (ZMod q) →* (B ⊗[U] D ≃ₐ[B] B ⊗[U] D) where
  toFun g := Algebra.TensorProduct.congr AlgEquiv.refl (act g)
  map_one' := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simp
    | add z w hz hw => simp_all [map_add (f := _)]
  map_mul' g h := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simp
    | add z w hz hw => simp_all [map_add (f := _)]

@[simp] theorem zmodTensorAct_tmul (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ)
    (D : Type) [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D))
    (b : B) (x : D) (g : Multiplicative (ZMod q)) :
    zmodTensorAct U B q D act g (b ⊗ₜ x) = b ⊗ₜ act g x := by simp [zmodTensorAct]

theorem isZModTorsor_tensorBase (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ)
    (D : Type) [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D))
    (hq : 0 < q) (hD : IsZModTorsor U D q act) :
    IsZModTorsor B (B ⊗[U] D) q (zmodTensorAct U B q D act) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨h1, h2, h3, h4⟩ := hD
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  set Φ := Algebra.TensorProduct.productMap
      (Pi.algHom U (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id U D))
      (Pi.algHom U (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)) with hΦ
  set ΦB := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => B ⊗[U] D) (fun _ => AlgHom.id B (B ⊗[U] D)))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => B ⊗[U] D)
        (fun g => (zmodTensorAct U B q D act g).toAlgHom)) with hΦB
  let e1 := TensorProduct.AlgebraTensorModule.distribBaseChange U B D D
  let L := (LinearEquiv.ofBijective Φ.toLinearMap h4).lTensor B
  let e2 := TensorProduct.piRight U U B (fun _ : Multiplicative (ZMod q) => D)
  have key : ∀ z, ΦB (e1 z) = e2 (L z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        funext g
        simp [e1, L, e2, hΦ, hΦB, Algebra.TensorProduct.productMap_apply_tmul]
      | add w w' hw hw' =>
        simp only [TensorProduct.tmul_add, map_add (f := _), hw, hw']
    | add z w hz hw => simp only [map_add (f := _), hz, hw]
  have : (ΦB : _ → _) = e2 ∘ L ∘ e1.symm := by
    funext w
    simpa using key (e1.symm w)
  rw [this]
  exact e2.bijective.comp (L.bijective.comp e1.symm.bijective)

theorem exists_isZModTorsor_tensorBase : ∀ (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type) [CommRing D]
    [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)), 0 < q →
    GlobalTheory.LocAcyc.IsZModTorsor U D q act →
    ∃ actB : Multiplicative (ZMod q) →* (TensorProduct U B D ≃ₐ[B] TensorProduct U B D),
      GlobalTheory.LocAcyc.IsZModTorsor B (TensorProduct U B D) q actB :=
  fun U B _ _ _ q D _ _ act hq hD => ⟨_, isZModTorsor_tensorBase U B q D act hq hD⟩

end GlobalTheory.LocAcyc
end
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem exists_common_multiple_mem_closure :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] (s : Finset D),
    ∃ a : A, a ≠ 0 ∧ ∀ d ∈ s,
      GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a) * d ∈ GlobalTheory.KeyOriginNoeth.closure A R D := by
  intro A R _ _ _ _ D _ _ _ s
  classical
  letI : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ d : D, ∃ a : A, a ≠ 0 ∧ IsIntegral R (baseHom A R D (algebraMap A R a) * d) := by
    intro d
    have hd : IsIntegral (GlobalTheory.LocAcyc.GenFib A R) d := Algebra.IsIntegral.isIntegral d
    obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (Rₘ := GlobalTheory.LocAcyc.GenFib A R) d hd
    obtain ⟨a, ha, rfl⟩ := hm
    refine ⟨a, nonZeroDivisors.ne_zero ha, ?_⟩
    exact hmi
  have hmem : ∀ x : D, IsIntegral R x → x ∈ closure A R D := fun x hx => hx
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert d s hds ih =>
    obtain ⟨a₂, ha₂, h₂⟩ := ih
    obtain ⟨a₁, ha₁, h₁⟩ := key d
    refine ⟨a₁ * a₂, mul_ne_zero ha₁ ha₂, ?_⟩
    intro e he
    apply hmem
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · have : baseHom A R D (algebraMap A R (a₁ * a₂)) * e =
          algebraMap R D (algebraMap A R a₂) * (baseHom A R D (algebraMap A R a₁) * e) := by
        simp only [map_mul]; show _ = baseHom A R D _ * _; ring
      rw [this]
      exact isIntegral_algebraMap.mul h₁
    · have : baseHom A R D (algebraMap A R (a₁ * a₂)) * e =
          algebraMap R D (algebraMap A R a₁) * (baseHom A R D (algebraMap A R a₂) * e) := by
        simp only [map_mul]; show _ = baseHom A R D _ * _; ring
      rw [this]
      exact isIntegral_algebraMap.mul (h₂ e he)

end GlobalTheory.KeyOriginNoeth
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem isEtaleAt_closure_of_disjoint : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    ∀ (Q : Ideal (GlobalTheory.KeyOriginNoeth.closure A R D)) [Q.IsPrime],
      (∀ a : A, a ≠ 0 → algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a) ∉ Q) →
      Algebra.IsEtaleAt R Q := by
  intro A R D _ _ _ _ _ _ _ _
  letI := closureAlg A R D
  intro Q _ hQ
  letI : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let SR : Submonoid R := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  let SC : Submonoid (closure A R D) := Algebra.algebraMapSubmonoid (closure A R D) SR
  have hCD : ∀ r : R, algebraMap (closure A R D) D (algebraMap R (closure A R D) r) = algebraMap R D r :=
    fun _ => rfl
  haveI : IsScalarTower R (closure A R D) D := IsScalarTower.of_algebraMap_eq (fun r => (hCD r).symm)
  have hunit : ∀ a : A, a ∈ nonZeroDivisors A → IsUnit (algebraMap R D (algebraMap A R a)) := by
    intro a ha
    have h1 : IsUnit (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) (algebraMap A R a)) :=
      IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A R) (⟨algebraMap A R a, a, ha, rfl⟩ : SR)
    rw [IsScalarTower.algebraMap_apply R (GlobalTheory.LocAcyc.GenFib A R) D]
    exact h1.map _
  haveI hloc : IsLocalization SC D := by
    refine (isLocalization_iff SC D).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩⟩
      exact hCD _ ▸ hunit a ha
    · intro d
      have hd : IsIntegral (GlobalTheory.LocAcyc.GenFib A R) d := Algebra.IsIntegral.isIntegral d
      obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization SR
        (Rₘ := GlobalTheory.LocAcyc.GenFib A R) d hd
      obtain ⟨a, ha, rfl⟩ := hm
      refine ⟨(⟨_, hmi⟩, ⟨algebraMap R (closure A R D) (algebraMap A R a), _, ⟨a, ha, rfl⟩, rfl⟩), ?_⟩
      show d * algebraMap (closure A R D) D (algebraMap R (closure A R D) (algebraMap A R a)) = _
      rw [hCD, mul_comm, ← Algebra.smul_def]
      rfl
    · intro x y h
      exact ⟨1, by rw [Subtype.ext h]⟩
  have hle : SC ≤ Q.primeCompl := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact hQ a (nonZeroDivisors.ne_zero ha)
  letI : Algebra D (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : IsScalarTower (closure A R D) D (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : IsLocalization (Algebra.algebraMapSubmonoid D Q.primeCompl) (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : Algebra.FormallyEtale D (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid D Q.primeCompl)
  haveI : Algebra.FormallyEtale R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.FormallyEtale.of_isLocalization SR
  haveI : Algebra.FormallyEtale R D := Algebra.FormallyEtale.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : IsScalarTower R D (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R (closure A R D) (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply (closure A R D) D (Localization.AtPrime Q), hCD])
  exact Algebra.FormallyEtale.comp R D (Localization.AtPrime Q)

end GlobalTheory.KeyOriginNoeth
end

section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

theorem filt_mul_filt_le (σ R : Type) [CommRing R] (I : Ideal R) (j k : ℕ) :
    filt (σ := σ) I j * filt I k ≤ filt I (j + k) := by
  classical
  refine Ideal.mul_le.2 fun F hF G hG => ?_
  rw [mem_filt] at hF hG ⊢
  intro α
  rw [MvPowerSeries.coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have hα : p.1 + p.2 = α := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : α.degree = p.1.degree + p.2.degree := by rw [← hα, map_add (f := _)]
  have h := Ideal.mul_mem_mul (hF p.1) (hG p.2)
  rw [← pow_add] at h
  exact Ideal.pow_le_pow_right (by omega) h

end GlobalTheory.FormalOrigin.Extend
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → SelfDual γ (A.map φ) → idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) → ∀ P Q : X →ₗ[R] X, (∀ x, P (P x) = P x) → (∀ x, Q (Q x) = Q x) → (∀ x, P (Q x) = 0) → (∀ x, Q (P x) = 0) → (∀ x y, γ (P x) y = γ x (Q y)) → (∀ a ∈ A, P a ∈ A) → (∀ a ∈ A, Q a ∈ A) → (∀ x, φ (P x) = P (φ x)) → (∀ x, φ (Q x) = Q (φ x)) → (∀ x, φ x - P (φ x) - Q (φ x) = x - P x - Q x) → ∃ n : ℕ, 0 < n ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ m, ℓ (T m) = (lam (idx A (A.map φ)))⁻¹ * (n : ℂ) * ℓ m := by
  first | exact @GlobalTheory.FinWeil.invariantForm_normOp_eq | exact GlobalTheory.FinWeil.invariantForm_normOp_eq | (intros; apply GlobalTheory.FinWeil.invariantForm_normOp_eq <;> assumption)
end
