module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle385
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle362
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABHasDerivAtY
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

open CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_etale_lift_genericFibre_of_factorization : ∀ (T R O : Type) [CommRing T] [CommRing R] [CommRing O] [Algebra T R] [Algebra R O]
    [Algebra T O] [IsScalarTower T R O],
    (∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
      ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
        (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g) →
    ∀ (U : Type) [CommRing U] [Algebra.FiniteType ℤ U] (u : U →+* GlobalTheory.LocAcyc.GenFib T O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra T W) (_ : IsScalarTower T R W)
      (_ : Algebra.Etale R W) (ψ : W →ₐ[R] O) (uW : U →+* GlobalTheory.LocAcyc.GenFib T W),
      (GlobalTheory.LocAcyc.genFibMap (ψ.restrictScalars T)).comp uW = u := by
  first | exact @GlobalTheory.GenFibLift.exists_etale_genFib_lift | exact GlobalTheory.GenFibLift.exists_etale_genFib_lift | (intros; apply GlobalTheory.GenFibLift.exists_etale_genFib_lift <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_point_closureFiniteEtale_strictHenselian : ∀ (A R O B : Type) [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Algebra A R]
    [CommRing O] [IsLocalRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] [CommRing B]
    (j : R →+* O) (β : O →+* B) (ψ : GlobalTheory.LocAcyc.GenFib A R →+* B),
    ψ.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = β.comp j →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D],
      Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D → GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A R D →
      ∃ σ : D →+* B, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) D) = ψ := by
  first | (exact @GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale) | (exact GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale) | (intros; apply GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale  <;> assumption)
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.Specialise

theorem sepEtale (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (Q : Ideal R) [Q.IsPrime] (L : Type) [Field L] [Algebra R L] [Algebra Q.ResidueField L]
    [IsScalarTower R Q.ResidueField L] (f : A →ₐ[R] L) (a : A) :
    IsSeparable Q.ResidueField (f a) := by
  let P : Ideal A := RingHom.ker f
  haveI : P.IsPrime := RingHom.ker_isPrime f
  have hPQ : Q = P.comap (algebraMap R A) := by
    ext r
    simp only [P, Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply R Q.ResidueField L]
    simp
  haveI : P.LiesOver Q := ⟨hPQ⟩
  letI := Localization.AtPrime.algebraOfLiesOver Q P
  have hsep : Algebra.IsSeparable Q.ResidueField P.ResidueField := inferInstance
  let g : P.ResidueField →ₐ[R] L := Ideal.ResidueField.liftₐ P f le_rfl (fun x hx => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.mpr (fun h => hx h))
  have hg : ∀ x : A, g (algebraMap A P.ResidueField x) = f x := fun x =>
    Ideal.ResidueField.liftₐ_algebraMap _ _ _ _ x
  let g' : P.ResidueField →ₐ[Q.ResidueField] L :=
    { g.toRingHom with
      commutes' := by
        have : g.toRingHom.comp (algebraMap Q.ResidueField P.ResidueField) =
            algebraMap Q.ResidueField L := by
          apply Ideal.ResidueField.ringHom_ext
          ext r
          simp only [RingHom.comp_apply]
          rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
            IsScalarTower.algebraMap_apply R A P.ResidueField]
          exact (hg _).trans (f.commutes r)
        intro c
        exact DFunLike.congr_fun this c }
  have h1 : g' (algebraMap A P.ResidueField a) = f a := hg a
  rw [← h1, isSeparable_map_iff g' g'.toRingHom.injective]
  exact Algebra.IsSeparable.isSeparable _ _

theorem specialisation_exists : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := by
  intro R S O _ _ _ _ _ _ _ _ Q y _ _ hQy hy hQ _ hpieces
  haveI : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
  haveI : (maximalIdeal S).LiesOver y := ⟨hy.symm⟩
  obtain ⟨Q₂, -, hQ₂p, hQ₂o⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := Q) (q := y) (maximalIdeal S) hQy
  haveI := hQ₂p
  letI : Algebra Q.ResidueField Q₂.ResidueField :=
    (Ideal.ResidueField.map Q Q₂ (algebraMap R S) hQ₂o.over).toAlgebra
  haveI : IsScalarTower R Q.ResidueField Q₂.ResidueField := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply]

  have hsepS : ∀ s : S, IsSeparable Q.ResidueField (algebraMap S Q₂.ResidueField s) := by
    intro s
    obtain ⟨ι, _, _, _, Si, -, hcov, hloc⟩ := hpieces
    obtain ⟨i, hi⟩ := hcov s
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    let F : Localization.AtPrime q →ₐ[R] Q₂.ResidueField :=
      (IsScalarTower.toAlgHom R S Q₂.ResidueField).comp ((Si i).val.comp (e : _ →ₐ[R] _))
    let f : A →ₐ[R] Q₂.ResidueField :=
      F.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨s, hi⟩)
    have hs : algebraMap S Q₂.ResidueField s = F (IsLocalization.mk' _ a t) := by
      simp only [F, AlgHom.comp_apply, hat]
      simp
    have hft : f t ≠ 0 := by
      have : IsUnit (f t) :=
        (IsLocalization.map_units (Localization.AtPrime q) t).map F
      exact this.ne_zero
    have hmul : F (IsLocalization.mk' _ a t) * f t = f a := by
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← map_mul,
        IsLocalization.mk'_spec]
    have hx : algebraMap S Q₂.ResidueField s = f a * (f t)⁻¹ := by
      rw [hs, eq_mul_inv_iff_mul_eq₀ hft, hmul]
    rw [hx, ← mem_separableClosure_iff]
    refine mul_mem ?_ (inv_mem ?_) <;> rw [mem_separableClosure_iff] <;>
      exact sepEtale R A Q _ f _
  haveI : Algebra.IsSeparable Q.ResidueField Q₂.ResidueField := ⟨fun x => by
    obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := S ⧸ Q₂) x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk,
      ← mem_separableClosure_iff]
    exact div_mem ((mem_separableClosure_iff).2 (hsepS u)) ((mem_separableClosure_iff).2 (hsepS v))⟩

  have hker : ∀ r : R, algebraMap R (ResidueField O) r = 0 ↔ r ∈ Q := by
    intro r
    rw [IsScalarTower.algebraMap_apply R O (ResidueField O), ResidueField.algebraMap_eq,
      residue_eq_zero_iff, ← hQ, Ideal.mem_comap]
  letI : Algebra Q.ResidueField (ResidueField O) :=
    (Ideal.ResidueField.lift Q (algebraMap R (ResidueField O)) (fun r hr => (hker r).2 hr)
      (fun r hr => by
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr (fun h => hr ((hker r).1 h)))).toAlgebra
  haveI : IsScalarTower R Q.ResidueField (ResidueField O) := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap Q _ _ _ r).symm
  let φ₀ : Q₂.ResidueField →ₐ[Q.ResidueField] ResidueField O := IsSepClosed.lift
  let ψ : S →ₐ[R] ResidueField O :=
    (φ₀.restrictScalars R).comp (IsScalarTower.toAlgHom R S Q₂.ResidueField)
  obtain ⟨φ, -⟩ := (GlobalTheory.IndEtaleHensel.bijective_residue_comp R S O hpieces).2 ψ
  exact ⟨φ⟩

end GlobalTheory.Specialise
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finite_integralClosureOverGenericFibre_of_etale : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Algebra A R] [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  first | (exact @GlobalTheory.KeyOriginNoeth.finite_closure) | (exact GlobalTheory.KeyOriginNoeth.finite_closure) | (intros; apply GlobalTheory.KeyOriginNoeth.finite_closure <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct


theorem _root_.GlobalTheory.T.closure_finite_over_base : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra A R], Function.Injective (algebraMap A R) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ _ _ hinj D _ _ _ _
  classical
  let GF := GlobalTheory.LocAcyc.GenFib A R
  let S := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  let K' := FractionRing R
  have hS : ∀ y : S, IsUnit (algebraMap R K' y) := by
    rintro ⟨y, a, ha, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    intro h0
    rw [IsFractionRing.to_map_eq_zero_iff] at h0
    have : a = 0 := hinj (by simpa using h0)
    exact nonZeroDivisors.ne_zero ha this
  let g : GF →+* K' := IsLocalization.lift (M := S) hS
  let : Algebra GF K' := g.toAlgebra
  have : IsScalarTower R GF K' :=
    IsScalarTower.of_algebraMap_eq (fun r => (IsLocalization.lift_eq (M := S) hS r).symm)
  have hg : Function.Injective (algebraMap GF K') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
    change g (IsLocalization.mk' GF r s) = 0 at hx
    show IsLocalization.mk' GF r s = 0
    rw [IsLocalization.lift_mk', mul_eq_zero] at hx
    rcases hx with hx | hx
    · rw [IsFractionRing.to_map_eq_zero_iff] at hx
      rw [hx, IsLocalization.mk'_zero]
    · exact absurd hx (Units.ne_zero _)
  let L' := K' ⊗[GF] D
  let ι : D →ₐ[GF] L' := Algebra.TensorProduct.includeRight
  have hι : Function.Injective ι := by
    have h1 : Function.Injective ((Algebra.linearMap GF K').rTensor D) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hg
    intro x y hxy
    apply (TensorProduct.lid GF D).symm.injective
    apply h1
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact hxy
  have key : (ι : D →+* L').comp (GlobalTheory.KeyOriginNoeth.baseHom A R D) = algebraMap R L' := by
    ext r
    show ι (algebraMap GF D (algebraMap R GF r)) = algebraMap R L' r
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply GF K' L', IsScalarTower.algebraMap_apply R K' L',
      ← IsScalarTower.algebraMap_apply R GF K']
  let : Algebra R (GlobalTheory.KeyOriginNoeth.closure A R D) :=
    GlobalTheory.KeyOriginNoeth.closureAlg A R D
  let Φ : GlobalTheory.KeyOriginNoeth.closure A R D →ₗ[R] integralClosure R L' :=
    { toFun := fun c => ⟨ι c.1, by
        have hc : (GlobalTheory.KeyOriginNoeth.baseHom A R D).IsIntegralElem c.1 := c.2
        obtain ⟨p, hp, he⟩ := hc
        refine ⟨p, hp, ?_⟩
        have h2 := Polynomial.hom_eval₂ p (GlobalTheory.KeyOriginNoeth.baseHom A R D) (ι : D →+* L') c.1
        rw [he, map_zero] at h2
        rw [← key]
        exact h2.symm⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show ι (x.1 + y.1) = ι x.1 + ι y.1
        exact map_add ι _ _
      map_smul' := fun r c => by
        apply Subtype.ext
        show ι (GlobalTheory.KeyOriginNoeth.baseHom A R D r * c.1) = r • ι c.1
        rw [map_mul, Algebra.smul_def]
        congr 1
        exact RingHom.congr_fun key r }
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    apply hι
    exact congrArg Subtype.val hxy
  have := GlobalTheory.ClosureFinite.integralClosure_finite_of_etale R K' L'
  have := isNoetherian_of_injective Φ hΦ
  exact Module.IsNoetherian.finite R _
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.isIntegrallyClosedIn_etale_genFib_of_injective : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra A R], Function.Injective (algebraMap A R) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    IsIntegrallyClosedIn (GlobalTheory.KeyOriginNoeth.closure A R D)
      (Localization (Algebra.algebraMapSubmonoid (GlobalTheory.KeyOriginNoeth.closure A R D)
        (nonZeroDivisors R))) := by
  first | (exact @GlobalTheory.KeyOriginNoeth.isIntegrallyClosedIn_closure_localization) | (exact GlobalTheory.KeyOriginNoeth.isIntegrallyClosedIn_closure_localization) | (intros; apply GlobalTheory.KeyOriginNoeth.isIntegrallyClosedIn_closure_localization  <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.heckeHankelTransformAB_differentiableOn_sigma : ∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.hTransAB_differentiableOn | exact GlobalTheory.HeckeTwo.hTransAB_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.hTransAB_differentiableOn <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open Classical


theorem _root_.GlobalTheory.T.heckeYDerivativeTerm_hasFDeriv_upperHalfPlane : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) →
    ∀ σ ∈ halfPlane, ∀ (q : Emb F → ℕ), ∀ z ∈ upperHalf F, ∀ τ₀ : Emb F,
    DifferentiableAt ℝ (termQ σ b ν q) z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ 1) = 2 * (Real.pi : ℂ) * I * ((τ₀ ν * τ₀ b : ℝ) : ℂ) * termQ σ b ν q z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ I) = ((τ₀ b : ℝ) : ℂ) * termQ σ b ν (q + Pi.single τ₀ 1) z := by
  first | exact @GlobalTheory.HeckeTwo.termQ_fderiv | exact GlobalTheory.HeckeTwo.termQ_fderiv | (intros; apply GlobalTheory.HeckeTwo.termQ_fderiv <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.iteratedDeriv_heckePhiTransform_hasDerivAt_holo : (∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y) → (∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane) →
  (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) := by
  first | exact @GlobalTheory.HeckeTwo.iteratedDeriv_hTrans_jet | exact GlobalTheory.HeckeTwo.iteratedDeriv_hTrans_jet | (intros; apply GlobalTheory.HeckeTwo.iteratedDeriv_hTrans_jet <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.heckeHankelTransformAB_hasDerivAt_y : ∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y := by
  first | exact @GlobalTheory.HeckeTwo.hTransAB_hasDerivAt | exact GlobalTheory.HeckeTwo.hTransAB_hasDerivAt | (intros; apply GlobalTheory.HeckeTwo.hTransAB_hasDerivAt <;> assumption)
end

section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

theorem _root_.GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le : ∀ (σ R : Type) [CommRing R] (I : Ideal R) (j k : ℕ), filt (σ := σ) I j * filt I k ≤ filt I (j + k) := by
  first | exact @GlobalTheory.FormalOrigin.Extend.filt_mul_filt_le | exact GlobalTheory.FormalOrigin.Extend.filt_mul_filt_le | (intros; apply GlobalTheory.FormalOrigin.Extend.filt_mul_filt_le <;> assumption)
end

section

open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_doublingJet_succ_of_lift : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → ∀ n : ℕ, 2 ≤ n → ∀ φ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ n φ → GlobalTheory.Nef.PathJet.IsRingHomMod π β (n + 1) ψ → (∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ f - φ f) → ∃ ψ' : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 1) ψ' ∧ ∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ' f - φ f := by
  first | exact @GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift | exact GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift | (intros; apply GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift <;> assumption)
end
