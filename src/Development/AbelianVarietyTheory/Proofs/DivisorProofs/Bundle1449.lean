module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal.FlatPlace

open MvPolynomial

instance isPrime_span_X_zero (m : ℕ) :
    (Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) ℂ)}).IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero 0)).2 prime_X

theorem exists_X_zero_pow_mul {m : ℕ} {f : MvPolynomial (Fin (m + 1)) ℂ} (hf : f ≠ 0) :
    ∃ (n : ℕ) (g : MvPolynomial (Fin (m + 1)) ℂ),
      g ∉ Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) ℂ)} ∧ f = X 0 ^ n * g := by
  obtain ⟨n, g, hg, e⟩ := WfDvdMonoid.max_power_factor hf
    (prime_X (R := ℂ) (i := (0 : Fin (m + 1)))).irreducible
  exact ⟨n, g, fun h => hg (Ideal.mem_span_singleton.1 h), e⟩

theorem isDVR_atPrime (m : ℕ) : IsDiscreteValuationRing
    (Localization.AtPrime (Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) ℂ)})) := by
  set q := Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) ℂ)}
  set D := Localization.AtPrime q
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0), ?_, ?_⟩
  · have hmax : IsLocalRing.maximalIdeal D = Ideal.span {algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0)} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
    have h0 : algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0) ≠ 0 := by
      intro h
      refine X_ne_zero (R := ℂ) (0 : Fin (m + 1)) ?_
      exact IsLocalization.injective D (M := q.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors q)
        (h.trans (map_zero _).symm)
    refine Prime.irreducible ?_
    rw [← Ideal.span_singleton_prime h0, ← hmax]
    infer_instance
  · intro x hx
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    have hf : f ≠ 0 := by
      rintro rfl
      exact hx (IsLocalization.mk'_zero _)
    obtain ⟨n, g, hg, rfl⟩ := exists_X_zero_pow_mul hf
    refine ⟨n, ?_⟩
    have hgu : IsUnit (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D g) := IsLocalization.map_units D (⟨g, hg⟩ : q.primeCompl)
    have hsu : IsUnit (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D s) := IsLocalization.map_units D s
    have e : IsLocalization.mk' D (X 0 ^ n * g) s * algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D s =
        algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0) ^ n * algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D g := by
      rw [IsLocalization.mk'_spec, map_mul, map_pow]
    show Associated _ (IsLocalization.mk' D (X 0 ^ n * g) s)
    refine (associated_mul_unit_left (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0) ^ n) _ hgu).symm.trans ?_
    rw [← e]
    exact associated_mul_unit_left _ _ hsu

end GlobalTheory.GraphLocal.FlatPlace

namespace GlobalTheory.GraphLocal.FlatPlace

open MvPolynomial

variable {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ]

theorem isUnit_of_ord_eq_zero {E : Place (algebraMap ℂ K)} (y : E.ring) (hy : (y : K) ≠ 0)
    (h0 : E.ord y = 0) : IsUnit y := by
  refine IsUnit.of_mul_eq_one (b := ⟨(y : K)⁻¹, (E.ord_nonneg_iff (inv_ne_zero hy)).1
    (by rw [E.ord_inv, h0]; simp)⟩) (Subtype.ext ?_)
  simp [hy]

theorem flat_aeval_placeAlg (k : ℕ) (R : Subring K)
    (π : R →+* κ) (E : Place (algebraMap ℂ K)) (hER : E.Contains R) (t : E.ring) (zR : Fin k → R) :
    (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
    (∀ a, algebraMap ℂ K a ∈ R) →
    (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
    Irreducible t → AlgebraicIndependent ℂ (fun i => π (zR i)) →
    (MvPolynomial.aeval (Fin.cons (⟨(t : K), t.2⟩ : placeAlg E)
        (fun i => (⟨(zR i : K), hER _ (zR i).2⟩ : placeAlg E))) :
        MvPolynomial (Fin (k + 1)) ℂ →ₐ[ℂ] placeAlg E).toRingHom.Flat := by
  intro hπ hc hord ht hind
  set x : Fin (k + 1) → placeAlg E := Fin.cons (⟨(t : K), t.2⟩ : placeAlg E)
    (fun i => (⟨(zR i : K), hER _ (zR i).2⟩ : placeAlg E)) with hx
  set φ := (MvPolynomial.aeval x : MvPolynomial (Fin (k + 1)) ℂ →ₐ[ℂ] placeAlg E)
  set q := Ideal.span {(X 0 : MvPolynomial (Fin (k + 1)) ℂ)}

  let cR : ℂ →+* R := (algebraMap ℂ K).codRestrict R hc
  have hπc : π.comp cR = algebraMap ℂ κ := RingHom.ext fun a => hπ a (hc a)

  have hC : ∀ g : MvPolynomial (Fin k) ℂ,
      φ ((finSuccEquiv ℂ k).symm (Polynomial.C g)) = aeval (fun i : Fin k => x i.succ) g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a =>
      rw [show (Polynomial.C (MvPolynomial.C a) : Polynomial (MvPolynomial (Fin k) ℂ)) =
        algebraMap ℂ _ a from rfl, AlgEquiv.commutes, AlgHom.commutes, aeval_C]
    | add p r hp hr => simp only [map_add, hp, hr]
    | mul_X p i hp =>
      rw [Polynomial.C_mul, map_mul, map_mul, hp, ← finSuccEquiv_X_succ, AlgEquiv.symm_apply_apply,
        map_mul, aeval_X, aeval_X]
  have hX : φ ((finSuccEquiv ℂ k).symm Polynomial.X) = x 0 := by
    rw [← finSuccEquiv_X_zero, AlgEquiv.symm_apply_apply, aeval_X]

  have key : ∀ f ∉ q, IsUnit (φ f) := by
    intro f hf
    set p := finSuccEquiv ℂ k f with hpdef
    set g := p.coeff 0
    have hfp : f = (finSuccEquiv ℂ k).symm p := by simp [p]
    have hp : p = Polynomial.X * p.divX + Polynomial.C g := (Polynomial.X_mul_divX_add p).symm
    have hg : g ≠ 0 := by
      intro h0
      apply hf
      rw [hfp, hp, h0, map_zero, add_zero, map_mul, ← finSuccEquiv_X_zero, AlgEquiv.symm_apply_apply]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

    set wR : R := eval₂ cR zR g
    have hwK : (wR : K) = (aeval (fun i : Fin k => x i.succ) g : placeAlg E) := by
      have e1 : (wR : K) = eval₂ (algebraMap ℂ K) (fun i => (zR i : K)) g :=
        eval₂_comp_left R.subtype cR zR g
      have e2 := (comp_aeval (R := ℂ) (fun i : Fin k => x i.succ) (placeAlg E).val).symm
      have e3 := congrArg (fun F : MvPolynomial (Fin k) ℂ →ₐ[ℂ] K => F g) e2
      simp only [AlgHom.comp_apply] at e3
      rw [e1]
      change _ = (placeAlg E).val (aeval (fun i : Fin k => x i.succ) g)
      rw [← e3]
      simp only [x, Fin.cons_succ]
      rfl
    have hπw : π wR ≠ 0 := by
      have e : π wR = aeval (fun i => π (zR i)) g := by
        rw [eval₂_comp_left π cR zR g, hπc]
        rfl
      rw [e]
      intro h0
      exact hg (hind (h0.trans (map_zero _).symm))
    have hw0 : (wR : K) ≠ 0 := by
      intro h0
      apply hπw
      rw [show wR = 0 from Subtype.ext h0, map_zero]
    have hwo : E.ord wR = 0 := by
      have h1 := (E.ord_nonneg_iff hw0).2 (hER _ wR.2)
      have h2 : ¬ 0 < E.ord wR := fun h => hπw ((hord wR hw0).2 h)
      omega
    set u : placeAlg E := aeval (fun i : Fin k => x i.succ) g
    set v : placeAlg E := φ ((finSuccEquiv ℂ k).symm p.divX)
    have hf' : φ f = x 0 * v + u := by
      rw [hfp, hp, map_add (f := _), map_mul, map_add (f := _), map_mul, hX, hC]
    let uE : E.ring := ⟨(u : K), u.2⟩
    let vE : E.ring := ⟨(v : K), v.2⟩
    have huE : IsUnit uE := isUnit_of_ord_eq_zero uE (by rw [← hwK] at *; simpa [uE, ← hwK] using hw0)
      (by simpa [uE, ← hwK] using hwo)
    let yE : E.ring := ⟨(φ f : K), (φ f).2⟩
    have hyE : yE = t * vE + uE := Subtype.ext (by simp [yE, uE, vE, hf', x])
    have hyu : IsUnit yE := by
      by_contra hn
      have hy : yE ∈ IsLocalRing.maximalIdeal E.ring := hn
      have htm : t ∈ IsLocalRing.maximalIdeal E.ring := ht.not_isUnit
      have : uE ∈ IsLocalRing.maximalIdeal E.ring := by
        have := sub_mem hy (Ideal.mul_mem_right vE _ htm)
        rwa [hyE, add_sub_cancel_left] at this
      exact this huE
    let toA : E.ring →+* placeAlg E :=
      { toFun := fun y => ⟨y, y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    exact hyu.map toA
  set D := Localization.AtPrime q
  haveI : IsDiscreteValuationRing D := isDVR_atPrime k
  have hunits : ∀ s : q.primeCompl, IsUnit (φ.toRingHom s) := fun s => key s.1 s.2
  let ℓ : D →+* placeAlg E := IsLocalization.lift (M := q.primeCompl) hunits
  have hcomp : ℓ.comp (algebraMap _ D) = φ.toRingHom := IsLocalization.lift_comp hunits
  have hφ0 : ∀ f, f ≠ 0 → φ f ≠ 0 := by
    intro f hf
    obtain ⟨n, g, hg, rfl⟩ := exists_X_zero_pow_mul hf
    rw [map_mul, map_pow]
    refine mul_ne_zero (pow_ne_zero _ ?_) (key g hg).ne_zero
    intro h
    apply ht.ne_zero
    have e : ((φ (X 0) : placeAlg E) : K) = t := by simp [φ, x]
    exact Subtype.ext (by rw [← e, h]; rfl)
  have hℓ : ℓ.Flat := by
    letI := ℓ.toAlgebra
    rw [RingHom.Flat, Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro a ha
    obtain ⟨⟨d, hd⟩, hda⟩ := (Submodule.mem_torsion_iff _).1 ha
    rw [Submodule.mem_bot]
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl d
    have hf : f ≠ 0 := by
      rintro rfl
      exact nonZeroDivisors.ne_zero hd (IsLocalization.mk'_zero _)
    have hℓd : ℓ (IsLocalization.mk' D f s) ≠ 0 := by
      intro h0
      have := (IsLocalization.lift_mk'_spec hunits f 0 s).1 h0
      exact hφ0 f hf (by simpa using this)
    simp only [Submonoid.mk_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hda
    exact (mul_eq_zero.1 hda).resolve_left hℓd
  have h := (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat D q.primeCompl)).comp hℓ
  rw [hcomp] at h
  exact h

end GlobalTheory.GraphLocal.FlatPlace
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

theorem ker_productMap_le_span {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ']
    (ρ : κ →ₐ[ℂ] κ') :
    RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) ≤
      Ideal.span {x | ∃ f : κ, x = f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f} := by
  have key : ∀ x : κ ⊗[ℂ] κ',
      x - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x ∈
        Ideal.span {x | ∃ f : κ, x = f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f} := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      have e : f ⊗ₜ[ℂ] g - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') (f ⊗ₜ g) =
          (f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f) * (1 ⊗ₜ g) := by
        simp [Algebra.TensorProduct.productMap_apply_tmul, sub_mul,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨f, rfl⟩)
    | add x y hx hy =>
      have e : x + y - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') (x + y) =
          (x - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x) +
            (y - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') y) := by
        rw [map_add (f := _), TensorProduct.tmul_add]
        abel
      rw [e]
      exact add_mem hx hy
  intro x hx
  have h := key x
  rwa [RingHom.mem_ker.1 hx, TensorProduct.tmul_zero, sub_zero] at h



theorem jets_mem_pow_sup : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  graphIdeal E R π ρ ≤ 𝔭 → Irreducible t →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i →
    ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
    w ∈ 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} := by

  intro K κ κ' _ _ _ _ _ _ R π ρ E 𝔭 _ t hle ht hπC hC hfrac hR hord M l a b w hw hx
  let T := tens (κ' := κ') (placeAlg E)
  let I : Ideal T := 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩}
  let q : T →ₐ[ℂ] T ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hq0 : ∀ y : T, q y = 0 ↔ y ∈ I := fun y => by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  let jL : placeAlg E →ₐ[ℂ] T :=
    (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom.comp Algebra.TensorProduct.includeLeft
  let jR : κ' →ₐ[ℂ] T :=
    (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hjL : ∀ e, (jL e : K ⊗[ℂ] κ') = (e : K) ⊗ₜ 1 := fun e => by
    simp [jL, tensMap]
  have hjR : ∀ c, (jR c : K ⊗[ℂ] κ') = 1 ⊗ₜ c := fun c => by
    simp [jR, tensMap]
  let ι : R →+* placeAlg E :=
    { toFun := fun r => ⟨r, hR _ r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hι : ∀ r : R, ((ι r : placeAlg E) : K) = r := fun _ => rfl

  have hg : ∀ r : R, jL (ι r) - jR (ρ (π r)) ∈ 𝔭 := fun r => by
    have e : ((jL (ι r) - jR (ρ (π r)) : T) : K ⊗[ℂ] κ') = (r : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π r) := by
      rw [Subalgebra.coe_sub, hjL (ι r), hjR (ρ (π r))]
      rfl
    exact hle (Ideal.subset_span (Or.inr ⟨r, e⟩))

  have hk : ∀ r : R, π r = 0 → q (jL (ι r)) = 0 := by
    intro r hr
    rw [hq0]
    apply Ideal.mem_sup_right
    by_cases h0 : (r : K) = 0
    · have e : jL (ι r) = 0 := Subtype.ext (by simp [hjL, hι, h0])
      rw [e]
      exact zero_mem _
    have hpos := (hord r h0).1 hr
    have hnu : ¬ IsUnit (⟨r, hR _ r.2⟩ : E.ring) := fun hu => by
      have h1 := E.ord_eq_zero hu
      simp only at h1
      omega
    have hm : (⟨r, hR _ r.2⟩ : E.ring) ∈ Ideal.span {t} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht]
      exact hnu
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hm
    rw [Ideal.mem_span_singleton']
    refine ⟨jL ⟨u, u.2⟩, Subtype.ext ?_⟩
    have hu' : (u : K) * t = r := congrArg Subtype.val hu
    simp only [Subalgebra.coe_mul, hjL, hι, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hu']

  have hu : ∀ r : R, π r ≠ 0 → IsUnit (q (jL (ι r))) := by
    intro r hr
    have hρ : IsUnit (q (jR (ρ (π r)))) :=
      ((isUnit_iff_ne_zero.2 ((map_ne_zero ρ).2 hr)).map jR).map q
    have hn : IsNilpotent (q (jL (ι r) - jR (ρ (π r)))) :=
      ⟨M, by rw [← map_pow, hq0]; exact Ideal.mem_sup_left (Ideal.pow_mem_pow (hg r) M)⟩
    have h := IsNilpotent.isUnit_add_left_of_commute hn hρ (Commute.all _ _)
    rwa [map_sub, add_sub_cancel] at h

  let φ : R →+* T ⧸ I := (q : T →+* T ⧸ I).comp ((jL : placeAlg E →+* T).comp ι)
  have hφ : ∀ r, φ r = q (jL (ι r)) := fun _ => rfl
  have hker : RingHom.ker π.rangeRestrict ≤ RingHom.ker φ := fun r hr => by
    rw [RingHom.mem_ker] at hr ⊢
    exact hk r (congrArg Subtype.val hr)
  let ψ : π.range →+* T ⧸ I :=
    π.rangeRestrict.liftOfRightInverse (Function.surjInv π.rangeRestrict_surjective)
      (Function.rightInverse_surjInv _) ⟨φ, hker⟩
  have hψ : ∀ r, ψ (π.rangeRestrict r) = q (jL (ι r)) := fun r =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
  haveI : IsFractionRing π.range κ := by
    refine ⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    · refine isUnit_iff_ne_zero.2 fun h => nonZeroDivisors.coe_ne_zero y (Subtype.ext h)
    · obtain ⟨c, d, hd, e⟩ := hfrac z
      exact ⟨(π.rangeRestrict c, ⟨π.rangeRestrict d, mem_nonZeroDivisors_of_ne_zero
        fun h => hd (congrArg Subtype.val h)⟩), e⟩
  have hunit : ∀ y : nonZeroDivisors π.range, IsUnit (ψ y) := by
    rintro ⟨⟨v, d, rfl⟩, hy⟩
    have hd : π d ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero ⟨_, hy⟩ (Subtype.ext h)
    exact (hψ d).symm ▸ hu d hd
  let θ₀ : κ →+* T ⧸ I := IsLocalization.lift (M := nonZeroDivisors π.range) hunit
  have hθ₀ : ∀ r, θ₀ (π r) = q (jL (ι r)) := fun r =>
    (IsLocalization.lift_eq (M := nonZeroDivisors π.range) hunit (π.rangeRestrict r)).trans (hψ r)

  let θ₀A : κ →ₐ[ℂ] T ⧸ I :=
    { θ₀ with
      commutes' := fun c => by
        have e1 : algebraMap ℂ κ c = π ⟨algebraMap ℂ K c, hC c⟩ := (hπC c (hC c)).symm
        have e2 : ι ⟨algebraMap ℂ K c, hC c⟩ = algebraMap ℂ (placeAlg E) c := Subtype.ext rfl
        change θ₀ (algebraMap ℂ κ c) = _
        rw [e1, hθ₀, e2, AlgHom.commutes, AlgHom.commutes] }
  let θ : κ ⊗[ℂ] κ' →ₐ[ℂ] T ⧸ I := Algebra.TensorProduct.productMap θ₀A (q.comp jR)
  have hθt : ∀ f c, θ (f ⊗ₜ c) = θ₀ f * q (jR c) := fun f c =>
    Algebra.TensorProduct.productMap_apply_tmul _ _ _ _

  have hwx : θ (∑ i, π (a i) ⊗ₜ[ℂ] b i) = q w := by
    have ew : w = ∑ i, jL (ι (a i)) * jR (b i) := by
      apply Subtype.ext
      rw [hw]
      simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, hjL, hjR, hι,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

    rw [ew, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hθt, hθ₀, map_mul]

  have hgen : Ideal.map θ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ≤
      Ideal.map q 𝔭 := by
    refine (Ideal.map_mono (ker_productMap_le_span ρ)).trans ?_
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
    obtain ⟨c, d, hd, e⟩ := hfrac f
    have hfd : θ₀ f * q (jL (ι d)) = q (jL (ι c)) := by rw [← hθ₀, ← hθ₀, ← map_mul, e]
    set u := θ (f ⊗ₜ 1 - 1 ⊗ₜ ρ f) with hu_def
    have hu1 : u = θ₀ f - q (jR (ρ f)) := by
      rw [hu_def, map_sub, hθt, hθt]
      simp only [map_one, mul_one, one_mul]
    have h2 : u * q (jL (ι d)) =
        q (jL (ι c) - jR (ρ (π c))) - q (jR (ρ f)) * q (jL (ι d) - jR (ρ (π d))) := by
      rw [hu1, sub_mul, hfd, ← e, map_mul ρ, map_mul jR, map_sub q (jL (ι c)), map_sub q (jL (ι d)),
        map_mul q]
      rw [mul_sub, sub_sub_sub_cancel_right]
    have h3 : u * q (jL (ι d)) ∈ Ideal.map q 𝔭 := by
      rw [h2]
      exact sub_mem (Ideal.mem_map_of_mem q (hg c))
        (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem q (hg d)))
    obtain ⟨v, hv⟩ := (hu d hd).exists_right_inv
    have h4 : u = u * q (jL (ι d)) * v := by rw [mul_assoc, hv, mul_one]
    rw [SetLike.mem_coe, h4]
    exact Ideal.mul_mem_right _ _ h3
  have hbot : Ideal.map q 𝔭 ^ M = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro y hy
    rw [RingHom.mem_ker]
    exact (hq0 y).2 (Ideal.mem_sup_left hy)
  have h1 := Ideal.mem_map_of_mem θ hx
  rw [Ideal.map_pow] at h1
  have h2 := Ideal.pow_right_mono hgen M h1
  rw [hbot, Ideal.mem_bot] at h2
  exact (hq0 w).1 (hwx.symm.trans h2)

end GlobalTheory.GraphLocal
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def diagonalBlockOfMatrix {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  ⅟(2 : AF F) • ((matD g).toBlocks₁₁ + (matD g).toBlocks₁₂ + (matD g).toBlocks₂₁ + (matD g).toBlocks₂₂)

def BigCell {σ : E →ₐ[F] E} {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (g : UD σ W) : Prop :=
  ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * diagonalBlockOfMatrix g = 1 ∧
    ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v

end GlobalTheory.DblVac
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.EvAdm

theorem exists_rational_rep_scaledInt : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ ξ : κ → F,
      r - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a := by
  intro F _ _ κ _ a _ r
  have hd : DenseRange (Pi.map fun (_ : κ) => algebraMap F (FiniteAdeleRing (𝓞 F) F)) :=
    DenseRange.piMap fun _ => PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 F) (K := F)
  have hop : IsOpen {y : κ → FiniteAdeleRing (𝓞 F) F | r - y ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    (GlobalTheory.EvAdm.isOpen_scaledInt a).preimage (continuous_const.sub continuous_id)
  have hr : r ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | r - y ∈ GlobalTheory.EvAdm.scaledInt F κ a} := by
    show r - r ∈ GlobalTheory.EvAdm.scaledInt F κ a
    rw [sub_self]
    exact zero_mem _
  obtain ⟨ξ, hξ⟩ := hd.exists_mem_open hop ⟨r, hr⟩
  exact ⟨ξ, hξ⟩

end GlobalTheory.EvAdm
end
