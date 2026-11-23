module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle328
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle120
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle356
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem GlobalTheory.herbrand_lattice_facts : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ev a τ (cofac a τ) ≠ 0 ∧ (∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0) ∧ LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) ∧ preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v) ∧ (preEig a Fil τ).map (mulR a N (lin a τ)) = filKer a Fil τ ∧ eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥ ∧ (eigSub a τ (Fin N → RS a)).map (comp a N τ) = (⊤ : Submodule (Int0 v) (Fin N → Int0 v)).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) (ev a τ (cofac a τ))) ∧ (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil) ∧ eigSub a τ (Fin N → RS a) ≤ preEig a Fil τ ∧ Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ ∧ (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0) ∧ (∃ g : RS a, ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x)) := by
  intro C _ v S _ _ a ha N Fil hFil τ
  obtain ⟨hfree, hfin, hlc, hev, hker, ⟨g, hg⟩, hann⟩ := GlobalTheory.T.adjoinRootProdLinearFactors_structure (Int0 v) S a τ
  have hd : ev a τ (cofac a τ) ≠ 0 := by
    rw [hev]
    exact Finset.prod_ne_zero_iff.mpr fun s hs =>
      sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hs (ha h).symm
  have hid : ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x) := by
    intro x
    have : cofac a τ • x = ev a τ (cofac a τ) • x + g • (lin a τ • x) := by
      conv_lhs => rw [hg]
      rw [add_smul, algebraMap_smul, mul_comm, mul_smul]
    rw [this, add_sub_cancel_right]
  have htf : ∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0 := by
    intro c x hc hx
    haveI := hfree
    haveI : Module.IsTorsionFree (Int0 v) (Fin N → RS a) :=
      (Module.Free.chooseBasis (Int0 v) (Fin N → RS a)).isTorsionFree
    exact (smul_eq_zero_iff_right hc).mp hx
  have hcomp0 : ∀ x : Fin N → RS a, comp a N τ x = 0 ↔ ∀ i, ev a τ (x i) = 0 := by
    intro x
    constructor
    · intro h i; exact congrFun h i
    · intro h; funext i; exact h i
  have h2 : ∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0 := by
    intro x
    rw [hcomp0]
    constructor
    · intro h
      show cofac a τ • x = 0
      funext i
      obtain ⟨r', hr'⟩ := hker _ (h i)
      show cofac a τ * x i = 0
      rw [hr', ← mul_assoc, mul_comm (cofac a τ), hlc, zero_mul]
    · intro h i
      have hi : cofac a τ * x i = 0 := congrFun h i
      have := congrArg (ev a τ) hi
      rw [map_mul, map_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hd
  have h3 : LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range, hcomp0]
    constructor
    · intro h
      choose r hr using fun i => hker _ (h i)
      exact ⟨r, funext fun i => (hr i).symm⟩
    · rintro ⟨y, rfl⟩ i
      show ev a τ (lin a τ * y i) = 0
      rw [map_mul, ev_lin, sub_self, zero_mul]
  have hcz : ∀ x : Fin N → RS a, comp a N τ x = 0 → cofac a τ • x = 0 := fun x h => (h2 x).mp h
  refine ⟨hd, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htf, ⟨g, hid⟩⟩
  ·
    rintro x ⟨hx1, hx2⟩
    have hx1' : lin a τ • x ∈ Fil := hx1
    have hc : cofac a τ • x = 0 := hcz x hx2
    apply hFil _ x hd
    rw [hid, hc, zero_sub]
    exact Fil.neg_mem (Fil.smul_mem g hx1')
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x ∈ Fil := hx
      refine ⟨hx', ?_⟩
      show cofac a τ • (lin a τ • x) = 0
      rw [smul_smul, mul_comm, hlc, zero_smul]
    · rintro ⟨hy1, hy2⟩
      have hy2' : mulR a N (cofac a τ) y = 0 := hy2
      have hk : y ∈ LinearMap.ker (comp a N τ) := (h2 y).mpr hy2'
      rw [h3] at hk
      obtain ⟨x, rfl⟩ := hk
      exact ⟨x, hy1, rfl⟩
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx1' : lin a τ • x = 0 := hx1
    have hc : cofac a τ • x = 0 := hcz x hx2
    have : ev a τ (cofac a τ) • x = 0 := by rw [hid, hc, hx1', smul_zero, sub_zero]
    exact (Submodule.mem_bot _).mpr (htf _ x hd this)
  · ext y
    simp only [Submodule.mem_map, Submodule.mem_top, true_and, LinearMap.lsmul_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x = 0 := hx
      choose c hc using fun i => hann (x i) (congrFun hx' i)
      refine ⟨c, funext fun i => ?_⟩
      show ev a τ (cofac a τ) * c i = ev a τ (x i)
      rw [hc i, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => algebraMap (Int0 v) (RS a) (c i) * cofac a τ, ?_, ?_⟩
      · show lin a τ • (fun i => algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = 0
        funext i
        show lin a τ * (algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = 0
        rw [mul_left_comm, hlc, mul_zero]
      · funext i
        show ev a τ (algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = ev a τ (cofac a τ) * c i
        rw [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  · ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x ∈ Fil := hx
      show lin a τ • Fil.mkQ x = 0
      rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx'
    · intro hq
      have hq' : lin a τ • q = 0 := hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Fil q
      refine ⟨x, ?_, rfl⟩
      show lin a τ • x ∈ Fil
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact hq'
  · intro x hx
    have hx' : lin a τ • x = 0 := hx
    show lin a τ • x ∈ Fil
    rw [hx']; exact Fil.zero_mem
  · intro x hx
    show lin a τ • x ∈ Fil
    exact Fil.smul_mem _ hx
end

section

open IsLocalRing Polynomial

noncomputable section
namespace GlobalTheory.FibreRetract

theorem exists_section_mod (T O : Type) [CommRing T] [IsLocalRing T] [HenselianLocalRing T]
    [IsAlgClosed (ResidueField T)] [CommRing O] [HenselianLocalRing O] [Algebra T O]
    [IsLocalHom (algebraMap T O)] (I : Ideal O) (hI : I ≠ ⊤)
    (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T) [IsLocalHom i]
    (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] (b : B →+* O ⧸ I)
    (hb : b.comp (algebraMap A B) = ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i) :
    ∃ s : B →+* T, s.comp (algebraMap A B) = i ∧
      ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp s = b := by
  haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (O ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : HenselianLocalRing (O ⧸ I) := GlobalTheory.henselianLocalRing_of_finite O (O ⧸ I)
  set π : T →+* O ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap T O) with hπ
  haveI : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact le_maximalIdeal hI)
  haveI : IsLocalHom π := inferInstance
  have het : (algebraMap A B).Etale := RingHom.etale_algebraMap.mpr inferInstance
  obtain ⟨ψ, hψ1, hψ2⟩ := GlobalTheory.T.etale_hom_to_field_factors_algClosed_subfield A B (ResidueField T) (ResidueField (O ⧸ I))
    ((residue T).comp i) (ResidueField.map π) ((residue (O ⧸ I)).comp b)
    (fun a ha => by
      simp only [RingHom.comp_apply, residue_eq_zero_iff]
      exact map_nonunit i a ha)
    (by
      ext a
      have := DFunLike.congr_fun hb a
      simp only [RingHom.comp_apply] at this ⊢
      rw [this, ResidueField.map_residue])
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.NCyc.StrictLocLift.lift_exists (algebraMap A B) het i ψ hψ1
  refine ⟨s, hs1, ?_⟩
  refine GlobalTheory.NCyc.StrictLocLift.lift_unique (algebraMap A B) het (π.comp i) _ _ ?_ hb ?_
  · rw [RingHom.comp_assoc, hs1]
  · ext x
    have h2 := DFunLike.congr_fun hψ2 x
    have h3 := DFunLike.congr_fun hs2 x
    simp only [RingHom.comp_apply] at h2 h3 ⊢
    rw [← h2, ← h3, ResidueField.map_residue]

end GlobalTheory.FibreRetract

namespace GlobalTheory.FibreRetract

theorem fibre_retract : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [HenselianLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    IsLocalHom (algebraMap T O) → algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA] (j : EA →+* O),
      j.comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (f : A →+* A₁) (i₁ : A₁ →+* T) (e : EA →+* A₁),
      Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp f = i ∧
      e.comp (algebraMap (Polynomial A) EA) = f.comp (Polynomial.evalRingHom 0) ∧
      ∀ x : EA, algebraMap T O (i₁ (e x)) - j x ∈ Ideal.span {algebraMap (Polynomial T) O Polynomial.X} := by
  intro T O _ _ _ _ _ _ _ _ hT hTO ht A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ j hj
  obtain ⟨hTh, hTac, -⟩ := GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩
  set I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X} with hIdef
  have hI : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal O).ne_top (top_le_iff.mp
    (h ▸ (Ideal.span_singleton_le_iff_mem _).mpr ht))
  letI : Algebra (Polynomial A) A := (Polynomial.evalRingHom 0).toAlgebra
  let B := TensorProduct (Polynomial A) A EA
  have hC : ∀ c : T, algebraMap (Polynomial T) O (Polynomial.C c) = algebraMap T O c := fun c => by
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O c, Polynomial.algebraMap_eq]
  let φ : Polynomial A →+* O ⧸ I :=
    (Ideal.Quotient.mk I).comp ((algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i))
  letI : Algebra (Polynomial A) (O ⧸ I) := φ.toAlgebra
  let f₁ : A →ₐ[Polynomial A] O ⧸ I :=
    { toRingHom := ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i
      commutes' := fun p => by
        change Ideal.Quotient.mk I (algebraMap T O (i (p.eval 0))) =
          Ideal.Quotient.mk I (algebraMap (Polynomial T) O (p.map i))
        rw [Ideal.Quotient.eq]
        obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p.map i)
        have h0 : (p.map i).coeff 0 = i (p.eval 0) := by
          rw [Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero]
        rw [h0] at hq
        rw [← hC, ← map_sub, ← neg_sub, hq, map_neg, map_mul]
        exact I.neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) }
  let f₂ : EA →ₐ[Polynomial A] O ⧸ I :=
    { toRingHom := (Ideal.Quotient.mk I).comp j
      commutes' := fun p => by
        change Ideal.Quotient.mk I (j (algebraMap (Polynomial A) EA p)) = φ p
        have := DFunLike.congr_fun hj p
        simp only [RingHom.comp_apply] at this
        simp only [φ, RingHom.comp_apply, this, Polynomial.coe_mapRingHom] }
  let b : B →+* O ⧸ I := (Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)).toRingHom
  have hb : b.comp (algebraMap A B) = ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i := by
    ext a
    change b (algebraMap A B a) = _
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
    exact (Algebra.TensorProduct.lift_tmul f₁ f₂ _ a 1).trans (by rw [map_one, mul_one]; rfl)
  haveI := hTh; haveI := hTac
  obtain ⟨s, hs1, hs2⟩ := exists_section_mod T O I hI A i B b hb
  let P : Ideal B := (maximalIdeal T).comap s
  haveI hP : P.IsPrime := Ideal.comap_isPrime s (maximalIdeal T)
  let A₁ := Localization.AtPrime P
  have hunit : ∀ y : P.primeCompl, IsUnit (s y) := fun y => by
    have hy : (y : B) ∉ P := y.2
    by_contra h
    exact hy ((IsLocalRing.mem_maximalIdeal _).mpr h)
  let i₁ : A₁ →+* T := IsLocalization.lift hunit
  have hi₁ : i₁.comp (algebraMap B A₁) = s := IsLocalization.lift_comp hunit
  let f : A →+* A₁ := algebraMap A A₁
  let e : EA →+* A₁ := (algebraMap B A₁).comp
    (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] B).toRingHom
  obtain ⟨hdom, hic⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale A P A₁
  haveI := hdom
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  haveI : IsNoetherianRing A₁ := IsLocalization.isNoetherianRing P.primeCompl A₁ inferInstance
  haveI : Algebra.EssFiniteType ℤ B := Algebra.EssFiniteType.comp ℤ A B
  haveI : Algebra.EssFiniteType B A₁ := Algebra.EssFiniteType.of_isLocalization A₁ P.primeCompl
  haveI : Algebra.EssFiniteType ℤ A₁ := Algebra.EssFiniteType.comp ℤ B A₁
  have hcomp : i₁.comp f = i := by
    rw [show f = (algebraMap B A₁).comp (algebraMap A B) from IsScalarTower.algebraMap_eq A B A₁,
      ← RingHom.comp_assoc, hi₁, hs1]
  have hloc : IsLocalHom i₁ := ⟨fun x hx => by
    obtain ⟨⟨b', y⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    have h1 : i₁ (IsLocalization.mk' A₁ b' y) * s y = s b' := by
      rw [← hi₁, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
    have h2 : IsUnit (s b') := h1 ▸ hx.mul (hunit y)
    intro hb'
    exact (IsLocalRing.mem_maximalIdeal _).mp hb' h2⟩
  haveI : Algebra.QuasiFinite A B := inferInstance
  haveI : Algebra.QuasiFinite A A₁ := inferInstance
  have hinj : Function.Injective i₁ := by
    have h1 : (RingHom.ker i₁).comap f = ⊥ := by
      rw [RingHom.comap_ker, hcomp]; exact (RingHom.injective_iff_ker_eq_bot i).mp hi
    have h2 : (⊥ : Ideal A₁).comap f = ⊥ := eq_bot_iff.mpr fun a ha => h1 ▸ Ideal.comap_mono bot_le ha
    haveI : (RingHom.ker i₁).IsPrime := RingHom.ker_isPrime i₁
    have := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) (⊥ : Ideal A₁) (RingHom.ker i₁) bot_le
      (by rw [Ideal.under, Ideal.under]; exact h2.trans h1.symm)
    exact (RingHom.injective_iff_ker_eq_bot i₁).mpr this.symm
  refine ⟨A₁, inferInstance, hdom, inferInstance, inferInstance, hic, ?_, f, i₁, e, hinj,
    hloc, hcomp, ?_, fun x => ?_⟩
  · convert ‹Algebra.EssFiniteType ℤ A₁› using 1
    exact Subsingleton.elim _ _
  · refine RingHom.ext fun p => ?_
    change algebraMap B A₁ (Algebra.TensorProduct.includeRight (algebraMap (Polynomial A) EA p)) =
      algebraMap A A₁ (p.eval 0)
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A B A₁]
    rfl
  · have h3 := DFunLike.congr_fun hs2 (Algebra.TensorProduct.includeRight x)
    have h4 : i₁ (e x) = s (Algebra.TensorProduct.includeRight x) := by
      rw [← hi₁]; rfl
    rw [h4]
    apply Ideal.Quotient.eq.mp
    refine h3.trans ?_
    change Algebra.TensorProduct.lift f₁ f₂ _ ((1 : A) ⊗ₜ x) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl

end GlobalTheory.FibreRetract
end
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.heckeWeightTwo_isGood_of_tsum : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (g : ι → ℂ → (Emb F → ℂ) → ℂ) (P : ℂ → (Emb F → ℂ) → ℂ),
  (∀ i, ∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (g i σ) (upperHalf F)) →
  (∀ i, ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (g i σ) z) halfPlane) →
  (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (g i σ) z‖ ≤ u i) →
  (∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F, P σ z = ∑' i, g i σ z) →
  IsGood P := by
  first | exact @GlobalTheory.HeckeTwo.isGood_of_tsum | exact GlobalTheory.HeckeTwo.isGood_of_tsum | (intros; apply GlobalTheory.HeckeTwo.isGood_of_tsum <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_heckeFourierFactor_le : (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ c c' : ℝ, 0 < c → ∀ k : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν β : ℝ, ν ≠ 0 → β ≠ 0 → ∀ w : ℂ, c ≤ w.im → w.im ≤ c' →
      ‖iteratedFDeriv ℝ k (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
          hTrans σ ν (β * w.im)) w‖ ≤ C * (|β| + |β|⁻¹) ^ m / (1 + |ν * β|) ^ N := by
  first | exact @GlobalTheory.HeckeTwo.FactorBound.norm_iteratedFDeriv_fourierFactor_le | exact GlobalTheory.HeckeTwo.FactorBound.norm_iteratedFDeriv_fourierFactor_le | (intros; apply GlobalTheory.HeckeTwo.FactorBound.norm_iteratedFDeriv_fourierFactor_le <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial Matrix

noncomputable section

namespace GlobalTheory.InertUnitOrb

theorem stdH_mulVec_eq_of_unitary {K : UQ} {n : ℕ} (u : Matrix (Fin n) (Fin n) K.E)
    (hu : (u.map K.c)ᵀ * u = 1) (a b : Fin n → K.E) :
    stdH K n (u *ᵥ a) (u *ᵥ b) = stdH K n a b := by
  have hu' : uᵀ * u.map K.c = 1 := by
    have := congrArg Matrix.transpose hu
    rwa [transpose_mul, transpose_transpose, transpose_one] at this
  have hS : ∀ y z : Fin n → K.E, stdH K n y z = y ⬝ᵥ (fun k => K.c (z k)) := fun _ _ => rfl
  have hc : (fun k => K.c ((u *ᵥ b) k)) = u.map K.c *ᵥ (fun k => K.c (b k)) := by
    funext k
    exact RingHom.map_mulVec (K.c : K.E →+* K.E) u b k
  rw [hS, hS, hc, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hu', vecMul_one]

theorem class_eq_of_conj :
    ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ γ' u : Matrix (Fin n) (Fin n) K.E)
      (x x' : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ →
      GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ' → (u.map K.c)ᵀ * u = 1 → γ * u = u * γ' → B.P.Separable →
      ∃ v : B.Aˣ, (x' : B.A) = x * (v * B.σ v) := by
  intro K B n γ γ' u x x' ψ ψ' ⟨_, hg, hh⟩ ⟨_, hg', hh'⟩ hu hγ hsep
  have hgen := GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable K B hsep
  let φ : B.A →ₗ[K.E] B.A := ψ.symm.toLinearMap ∘ₗ Matrix.toLin' u ∘ₗ ψ'.toLinearMap
  have hφ_apply : ∀ y, φ y = ψ.symm (u *ᵥ ψ' y) := fun y => by
    simp [φ, Matrix.toLin'_apply]
  have hψg : ∀ w, ψ.symm (γ *ᵥ w) = B.g * ψ.symm w := fun w => by
    apply ψ.injective
    rw [hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hφg : ∀ y, φ (B.g * y) = B.g * φ y := fun y => by
    rw [hφ_apply, hφ_apply, hg', mulVec_mulVec, ← hγ, ← mulVec_mulVec, hψg]
  have hpow : ∀ (k : ℕ) y, φ (B.g ^ k * y) = B.g ^ k * φ y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [pow_succ', mul_assoc, hφg, ih, ← mul_assoc]
  have hφp : ∀ (f : K.E[X]) y, φ (aeval B.g f * y) = aeval B.g f * φ y := by
    intro f
    induction f using Polynomial.induction_on' with
    | add p q hp hq => intro y; rw [map_add (f := _), add_mul, add_mul, map_add (f := _), hp, hq]
    | monomial k e =>
      intro y
      rw [aeval_monomial, mul_assoc, ← Algebra.smul_def, map_smul, hpow, Algebra.smul_def, mul_assoc]
  have hφ : ∀ y, φ y = y * φ 1 := fun y => by
    obtain ⟨f, rfl⟩ := hgen y
    simpa using hφp f 1

  have hu2 : u * (u.map K.c)ᵀ = 1 := mul_eq_one_comm.mp hu
  have hy0 : φ (ψ'.symm ((u.map K.c)ᵀ *ᵥ ψ 1)) = 1 := by
    rw [hφ_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec, hu2, one_mulVec,
      LinearEquiv.symm_apply_apply]
  have hunit : IsUnit (φ 1) := by
    have h1 : ψ'.symm ((u.map K.c)ᵀ *ᵥ ψ 1) * φ 1 = 1 := by rw [← hφ, hy0]
    exact ⟨⟨φ 1, ψ'.symm ((u.map K.c)ᵀ *ᵥ ψ 1), by rw [mul_comm]; exact h1, h1⟩, rfl⟩
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]

  have hiso : ∀ y z, B.herm x' y z = B.herm x (y * φ 1) (z * φ 1) := fun y z => by
    rw [← hh', ← stdH_mulVec_eq_of_unitary u hu, ← hh, ← hφ, ← hφ, hφ_apply, hφ_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have key : ∀ y, Algebra.trace K.E B.A (((x' : B.A) - x * (φ 1 * B.σ (φ 1))) * y) = 0 := fun y => by
    have h1 := hiso y 1
    simp only [InvAlg.herm, map_one, mul_one, one_mul] at h1
    rw [sub_mul, map_sub, h1, sub_eq_zero]
    congr 1
    ring
  exact sub_eq_zero.mp (GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hsep hgen _ key)

end GlobalTheory.InertUnitOrb
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem coord_bijective_of_le_affine : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W W' : Z.affineOpens), (W' : Z.Opens) ≤ W → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W) → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W') := by
  intro A B _ _ _ N r e σ Z y W W' hle hW
  have hbas : ∀ f : Γ(Z, W), Function.Bijective (coord A B e σ y (Z.basicOpen f)) := by
    intro f
    rw [GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W f]
    exact ⟨LocalizedModule.map_injective _ _ hW.1, LocalizedModule.map_surjective _ _ hW.2⟩
  let s : Set Γ(Z, W') := {g | Function.Bijective (coord A B e σ y (Z.basicOpen g))}
  have hspan : Ideal.span s = ⊤ := by
    rw [← W'.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter W.2 W'.2 x ⟨hle hx, hx⟩
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, ?_⟩, ?_⟩
    · show Function.Bijective _
      rw [← hfg]; exact hbas f
    · show x ∈ Z.basicOpen g
      rw [← hfg]; exact hxf
  exact bijective_of_localized_span s hspan _ fun g => (GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W' g.1).1 g.2

end GlobalTheory.HilbAff
end
