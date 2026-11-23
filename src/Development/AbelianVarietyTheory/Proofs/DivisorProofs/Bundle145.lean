module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.WittVector.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Teichmuller
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Unramified.Pi
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Unramified.LocalRing

@[expose] public section

section

open scoped TensorProduct Classical

namespace GlobalTheory

theorem tensor_centralizer_flat : ∀ (K : Type) [Field K] [Algebra ℚ K] (C : Type) [Ring C] [Algebra ℚ C] (y : C),
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val) ∧
    ∀ w : K ⊗[ℚ] C, Commute w ((1 : K) ⊗ₜ[ℚ] y) → ∃ w' : K ⊗[ℚ] (Subalgebra.centralizer ℚ ({y} : Set C)),
      Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val w' = w := by
  intro K _ _ C _ _ y
  set Z := Subalgebra.centralizer ℚ ({y} : Set C) with hZ
  have hmap : ∀ w', Algebra.TensorProduct.map (AlgHom.id K K) Z.val w'
      = LinearMap.lTensor K Z.val.toLinearMap w' := by
    intro w'
    induction w' using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  let ad : C →ₗ[ℚ] C := LinearMap.mulRight ℚ y - LinearMap.mulLeft ℚ y
  have hex : Function.Exact Z.val.toLinearMap ad := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have : x * g - g * x = 0 := by simpa [ad] using hx
      exact (sub_eq_zero.mp this).symm
    · rintro ⟨z, rfl⟩
      have hz := z.2
      rw [Subalgebra.mem_centralizer_iff] at hz
      have := hz y (Set.mem_singleton y)
      simp [ad, this]
  have hexK := Module.Flat.lTensor_exact K hex
  have hadK : ∀ w : K ⊗[ℚ] C, LinearMap.lTensor K ad w = w * ((1 : K) ⊗ₜ[ℚ] y) - ((1 : K) ⊗ₜ[ℚ] y) * w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ad, TensorProduct.tmul_sub]
    | add a b ha hb => rw [map_add (f := _), ha, hb, add_mul, mul_add]; abel
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [hmap, hmap] at hab
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective hab
  · intro w hw
    have h0 : LinearMap.lTensor K ad w = 0 := by
      rw [hadK, hw.eq, sub_self]
    obtain ⟨w', hw'⟩ := (hexK w).mp h0
    exact ⟨w', by rw [hmap]; exact hw'⟩

end GlobalTheory
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem algebraTrace_map_of_cokernel_killed (S A B : Type) [CommRing S] [IsDomain S] [CommRing A]
    [Algebra S A] [Module.Free S A] [Module.Finite S A] [CommRing B] [Algebra S B]
    [Module.Free S B] [Module.Finite S B] (φ : A →ₐ[S] B) (hφ : Function.Injective φ)
    (s : S) (hs : s ≠ 0) (hr : ∀ b : B, s • b ∈ φ.range) (x : A) :
    Algebra.trace S B (φ x) = Algebra.trace S A x := by
  classical
  choose g hg using fun b => (AlgHom.mem_range φ).1 (hr b)
  let gl : B →ₗ[S] A :=
    { toFun := g
      map_add' := by
        intro b c
        apply hφ
        rw [map_add (f := _), hg, hg, hg, smul_add]
      map_smul' := by
        intro r b
        apply hφ
        rw [hg, RingHom.id_apply, map_smul, hg, smul_comm] }
  have h1 : φ.toLinearMap ∘ₗ gl = s • LinearMap.id := by
    ext b
    simp [gl, hg]
  have h2 : gl ∘ₗ φ.toLinearMap = s • LinearMap.id := by
    ext a
    apply hφ
    simp [gl, hg]
  have h3 : Algebra.lmul S B (φ x) ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ Algebra.lmul S A x := by
    ext a
    simp
  have key : s * Algebra.trace S B (φ x) = s * Algebra.trace S A x := by
    rw [Algebra.trace_apply, Algebra.trace_apply]
    calc s * LinearMap.trace S B (Algebra.lmul S B (φ x))
        = LinearMap.trace S B (Algebra.lmul S B (φ x) ∘ₗ (φ.toLinearMap ∘ₗ gl)) := by
          rw [h1, LinearMap.comp_smul, LinearMap.comp_id, map_smul, smul_eq_mul]
      _ = LinearMap.trace S B (φ.toLinearMap ∘ₗ (Algebra.lmul S A x ∘ₗ gl)) := by
          rw [← LinearMap.comp_assoc, h3, LinearMap.comp_assoc]
      _ = LinearMap.trace S A ((Algebra.lmul S A x ∘ₗ gl) ∘ₗ φ.toLinearMap) := by
          rw [LinearMap.trace_comp_comm']
      _ = s * LinearMap.trace S A (Algebra.lmul S A x) := by
          rw [LinearMap.comp_assoc, h2, LinearMap.comp_smul, LinearMap.comp_id, map_smul,
            smul_eq_mul]
  exact mul_left_cancel₀ hs key

end GlobalTheory
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.FinRedTensor

theorem formallyUnramified_int_of_finite_field (K : Type) [Field K] [Finite K] :
    Algebra.FormallyUnramified ℤ K := by
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : NeZero p := ⟨CharP.char_ne_zero_of_finite K p⟩
  haveI : Fact p.Prime := CharP.char_is_prime_of_pos K p
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  haveI : Module.Finite (ZMod p) K := Module.Finite.of_finite
  haveI : Algebra.IsSeparable (ZMod p) K := inferInstance
  haveI : Algebra.FormallyUnramified (ZMod p) K := Algebra.FormallyUnramified.of_isSeparable _ _
  haveI : Algebra.FormallyUnramified ℤ (ZMod p) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (ZMod p)) (ZMod.intCast_surjective)
  exact Algebra.FormallyUnramified.comp ℤ (ZMod p) K

theorem formallyUnramified_int_of_finite_isReduced (A : Type) [CommRing A] [Finite A]
    [IsReduced A] : Algebra.FormallyUnramified ℤ A := by
  haveI : IsArtinianRing A := inferInstance
  have h : Algebra.FormallyUnramified ℤ (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) := by
    rw [Algebra.FormallyUnramified.pi_iff]
    intro I
    have := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    haveI : Finite (A ⧸ I.asIdeal) :=
      Finite.of_surjective (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective
    exact formallyUnramified_int_of_finite_field _
  exact Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi A).restrictScalars ℤ).symm

theorem isReduced_field_tensor_finite :
    ∀ (A : Type) [CommRing A] [Finite A] [IsReduced A] (k : Type) [Field k],
      IsReduced (k ⊗[ℤ] A) := by
  intro A _ _ _ k _
  haveI := formallyUnramified_int_of_finite_isReduced A
  haveI : Algebra.FormallyUnramified k (k ⊗[ℤ] A) := Algebra.FormallyUnramified.base_change k
  haveI : Module.Finite ℤ A := Module.Finite.of_finite
  haveI : Algebra.EssFiniteType k (k ⊗[ℤ] A) := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field k _

end GlobalTheory.FinRedTensor
end

section

open Algebra

namespace GlobalTheory

theorem exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified :
    ∀ (P D : Type) [CommRing P] [IsDomain P] [CommRing D] [IsDomain D] [Algebra P D]
      [Algebra.FiniteType P D] [Algebra.FormallyUnramified P D] (f : D), f ≠ 0 →
      ∃ Q : P, Q ≠ 0 ∧ ∃ d : D, algebraMap P D Q = f * d := by
  intro P D _ _ _ _ _ _ _ f hf
  by_cases hinj : Function.Injective (algebraMap P D)
  swap
  · rw [injective_iff_map_eq_zero] at hinj
    push_neg at hinj
    obtain ⟨Q, hQ, hQ0⟩ := hinj
    exact ⟨Q, hQ0, 0, by rw [hQ, mul_zero]⟩
  let M := nonZeroDivisors P
  let K := FractionRing P
  let S := Algebra.algebraMapSubmonoid D M
  let L := Localization S
  letI : Algebra K L := localizationAlgebra M D
  haveI : IsScalarTower P K L := inferInstance
  have hS : S ≤ nonZeroDivisors D := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hq))
  haveI : IsDomain L := IsLocalization.isDomain_localization hS
  have hDL : Function.Injective (algebraMap D L) := IsLocalization.injective L hS
  haveI : IsLocalization (M.map (algebraMap P D)) L := inferInstanceAs (IsLocalization S L)
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.localization_map M (S := D)
  haveI : Algebra.EssFiniteType D L := Algebra.EssFiniteType.of_isLocalization L S
  haveI : Algebra.EssFiniteType P L := Algebra.EssFiniteType.comp P D L
  haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp P K L
  haveI : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  have hint : IsIntegral K (algebraMap D L f) := Algebra.IsIntegral.isIntegral _
  have hne : algebraMap D L f ≠ 0 := (map_ne_zero_iff _ hDL).2 hf
  obtain ⟨u, hu⟩ := hint.isUnit hne
  have hy : algebraMap D L f * ↑u⁻¹ = 1 := by rw [← hu]; exact u.mul_inv
  obtain ⟨⟨d, s⟩, hds⟩ := IsLocalization.surj S (↑u⁻¹ : L)
  obtain ⟨q, hq, hqs⟩ := s.2
  refine ⟨q, nonZeroDivisors.ne_zero hq, d, ?_⟩
  apply hDL
  simp only at hds
  rw [map_mul, ← hds, ← mul_assoc, hy, one_mul, hqs]

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem map_comap_maximalIdeal_eq_of_formallyUnramified
    (A B : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] :
    ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := by
  set p := (maximalIdeal B).comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let A' := Localization.AtPrime p
  have hg : ∀ y : p.primeCompl, IsUnit (algebraMap A B y) := by
    intro y
    have : (y : A) ∉ p := y.2
    exact IsLocalRing.notMem_maximalIdeal.mp this
  let f : A' →+* B := IsLocalization.lift (M := p.primeCompl) hg
  letI : Algebra A' B := f.toAlgebra
  haveI : IsScalarTower A A' B := IsScalarTower.of_algebraMap_eq
    (fun x => (IsLocalization.lift_eq (M := p.primeCompl) hg x).symm)
  haveI : IsLocalHom (algebraMap A' B) := by
    constructor
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    have e : IsLocalization.mk' A' a s * algebraMap A A' s = algebraMap A A' a :=
      IsLocalization.mk'_spec A' a s
    have hs : IsUnit (algebraMap A' B (algebraMap A A' s)) := by
      rw [← IsScalarTower.algebraMap_apply]; exact hg s
    have ha : IsUnit (algebraMap A B a) := by
      rw [IsScalarTower.algebraMap_apply A A' B, ← e, map_mul]; exact hx.mul hs
    have ha' : a ∈ p.primeCompl := by
      show a ∉ p
      rw [hp, Ideal.mem_comap]
      exact IsLocalRing.notMem_maximalIdeal.mpr ha
    have hu : IsUnit (algebraMap A A' a) := IsLocalization.map_units A' (⟨a, ha'⟩ : p.primeCompl)
    rw [← e] at hu
    exact isUnit_of_mul_isUnit_left hu
  haveI : Algebra.FormallyUnramified A' B := .of_restrictScalars A A' B
  haveI : Algebra.EssFiniteType A' B := .of_comp A A' B
  have h := Algebra.FormallyUnramified.map_maximalIdeal (R := A') (S := B)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq] at h
  exact h

end GlobalTheory
end

section

open MvPolynomial

namespace GlobalTheory

theorem isIntegral_coneRing_of_forall_valuationSubring :
    ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e : ℕ) (w : Fin r → K) (τ : K), (∀ V : ValuationSubring K, (∀ c, φ c ∈ V) → ∃ i, w i ≠ 0 ∧ τ / w i ^ e ∈ V) → ∃ (m : ℕ) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 := by
  intro F K _ _ φ r e w τ h
  classical
  let L := FractionRing (Polynomial K)
  let j : Polynomial K →+* L := algebraMap (Polynomial K) L
  let g : MvPolynomial (Fin r) F →+* Polynomial K :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X)
  let y : Polynomial K := Polynomial.C τ * Polynomial.X ^ e
  have hjinj : Function.Injective j := IsFractionRing.injective _ _
  have hx : j y ∈ (integralClosure (Subring.closure (Set.range (j.comp g))) L).toSubring := by
    rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
    intro V
    obtain ⟨W, hW⟩ := V
    change j y ∈ W
    let U : ValuationSubring K := W.comap (j.comp Polynomial.C)
    have hU : ∀ c, φ c ∈ U := by
      intro c
      have : j (g (MvPolynomial.C c)) ∈ W := hW ⟨_, rfl⟩
      simpa [g, U] using this
    obtain ⟨i, hi, hτ⟩ := h U hU
    have h1 : j (Polynomial.C (w i) * Polynomial.X) ∈ W := by
      have : j (g (MvPolynomial.X i)) ∈ W := hW ⟨_, rfl⟩
      simpa [g] using this
    have h2 : j (Polynomial.C (τ / w i ^ e)) ∈ W := hτ
    have hy : y = Polynomial.C (τ / w i ^ e) * (Polynomial.C (w i) * Polynomial.X) ^ e := by
      rw [mul_pow, ← mul_assoc, ← Polynomial.C_pow, ← Polynomial.C_mul,
        div_mul_cancel₀ _ (pow_ne_zero _ hi)]
    rw [hy, map_mul, map_pow]
    exact mul_mem h2 (pow_mem h1 _)
  have hcl : Subring.closure (Set.range (j.comp g)) = (j.comp g).range := by
    rw [← RingHom.coe_range]; exact Subring.closure_eq _
  rw [hcl] at hx
  have hint : IsIntegral (j.comp g).range (j y) := hx
  obtain ⟨p, hp, hpx⟩ := hint
  have hb : ∀ k : Fin p.natDegree, ∃ b : MvPolynomial (Fin r) F, j (g b) = (p.coeff k : L) :=
    fun k => (p.coeff k).2
  choose b hb using hb
  refine ⟨p.natDegree, b, hjinj ?_⟩
  have e1 := hpx
  rw [hp.as_sum] at e1
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at e1
  rw [Finset.sum_range (fun k => algebraMap (j.comp g).range L (p.coeff k) * j y ^ k)] at e1

  rw [map_zero, ← e1, map_add (f := _), map_sum, map_pow]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow]
  exact congrArg (· * j y ^ (k : ℕ)) (hb k)

end GlobalTheory
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem wittVector_dvd_of_coeff_zero_eq_zero (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (a : WittVector p k) (ha : a.coeff 0 = 0) :
    (p : WittVector p k) ∣ a := by
  by_cases h0 : a = 0
  · exact h0 ▸ dvd_zero _
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul a h0
  cases m with
  | zero =>
    exfalso
    simp only [pow_zero, one_mul] at ha
    exact hb ha
  | succ n => exact ⟨(p : WittVector p k) ^ n * b, by ring⟩

theorem wittVector_natCast_ne_zero (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] : (p : WittVector p k) ≠ 0 := by
  intro h
  have := WittVector.coeff_p_pow p k 1
  rw [pow_one, h] at this
  simp at this

theorem exists_flat_lift_mod_p_sq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectField k], ∃ (Λ : Type) (_ : CommRing Λ) (π : Λ →+* k), Function.Surjective π ∧
      RingHom.ker π = Ideal.span {(p : Λ)} ∧ (p : Λ) ^ 2 = 0 ∧
      ∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)} := by
  intro p _ k _ _ _
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  set I : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k) ^ 2} with hI
  have hlift : ∀ a ∈ I, WittVector.constantCoeff a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    simp [map_mul, map_pow, map_natCast, CharP.cast_eq_zero]
  let π : (WittVector p k ⧸ I) →+* k := Ideal.Quotient.lift I WittVector.constantCoeff hlift
  have hπ : ∀ a, π (Ideal.Quotient.mk I a) = a.coeff 0 := by
    intro a
    simp [π, Ideal.Quotient.lift_mk, WittVector.constantCoeff_apply]
  have hp0 : π (p : WittVector p k ⧸ I) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero k p
  refine ⟨WittVector p k ⧸ I, inferInstance, π, ?_, ?_, ?_, ?_⟩
  · intro r
    refine ⟨Ideal.Quotient.mk I (WittVector.teichmuller p r), ?_⟩
    rw [hπ, WittVector.teichmuller_coeff_zero]
  · ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, hπ, Ideal.mem_span_singleton]
    constructor
    · intro ha
      obtain ⟨c, rfl⟩ := wittVector_dvd_of_coeff_zero_eq_zero p k a ha
      exact ⟨Ideal.Quotient.mk I c, by rw [map_mul, map_natCast]⟩
    · rintro ⟨c, hc⟩
      rw [← hπ, hc, map_mul, hp0, zero_mul]
  · rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_natCast (Ideal.Quotient.mk I), ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    have hpne := wittVector_natCast_ne_zero p k
    have hac : a = (p : WittVector p k) * c := by
      apply mul_left_cancel₀ hpne
      rw [hc]; ring
    rw [Ideal.mem_span_singleton]
    exact ⟨Ideal.Quotient.mk I c, by rw [hac, map_mul, map_natCast]⟩

end GlobalTheory
end
