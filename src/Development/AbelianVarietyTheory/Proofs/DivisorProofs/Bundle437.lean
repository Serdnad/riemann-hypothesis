module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle351
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle385
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle234
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle238
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle388
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
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthSumHeightOneDisjointDivisors
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

namespace GlobalTheory

theorem exists_common_denominator_of_fg {R L : Type*} [CommRing R] [IsDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (N : Submodule R L) (hN : N.FG) :
    ∃ c : R, c ≠ 0 ∧ ∀ y ∈ N, ∃ s : R, algebraMap R L s = c • y := by
  obtain ⟨c, hc, h⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) hN
  exact ⟨c, nonZeroDivisors.ne_zero hc, fun y hy => h y hy⟩

theorem exists_ne_zero_mul_mem_of_isIntegral_of_fraction (K R B : Type) [Field K] [CharZero K]
    [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] [CommRing B] [IsDomain B]
    [Algebra R B] (hinj : Function.Injective (algebraMap R B)) :
    ∃ c : R, c ≠ 0 ∧ ∀ x : B, IsIntegral R x →
      (∃ r s : R, r ≠ 0 ∧ algebraMap R B r * x = algebraMap R B s) →
      ∃ s : R, algebraMap R B c * x = algebraMap R B s := by
  let L := FractionRing R
  let M := FractionRing B
  haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI hfin : Module.Finite R (integralClosure R L) := finite_integralClosure_dedekind K R L L
  have hfg : (Subalgebra.toSubmodule (integralClosure R L)).FG :=
    Module.Finite.iff_fg.mp hfin
  obtain ⟨c, hc, h⟩ := exists_common_denominator_of_fg _ hfg
  refine ⟨c, hc, fun x hx ⟨r, s, hr, hrs⟩ => ?_⟩
  letI : Algebra L M := FractionRing.liftAlgebra R M
  let φ : L →ₐ[R] M := IsScalarTower.toAlgHom R L M
  have hφ : Function.Injective φ := φ.toRingHom.injective
  have hB : Function.Injective (algebraMap B M) := IsFractionRing.injective B M
  have hrM : algebraMap R M r ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R B M]
    exact (map_ne_zero_iff _ hB).mpr ((map_ne_zero_iff _ hinj).mpr hr)
  have hy : φ (algebraMap R L s / algebraMap R L r) = algebraMap B M x := by
    rw [map_div₀, AlgHom.commutes, AlgHom.commutes, div_eq_iff hrM,
      IsScalarTower.algebraMap_apply R B M, IsScalarTower.algebraMap_apply R B M, ← hrs, map_mul,
      mul_comm]
  have hint : IsIntegral R (algebraMap R L s / algebraMap R L r) := by
    rw [← isIntegral_algHom_iff φ hφ, hy]
    exact hx.map (IsScalarTower.toAlgHom R B M)
  obtain ⟨t, ht⟩ := h _ hint
  refine ⟨t, hB ?_⟩
  have := congrArg φ ht
  rw [map_smul, hy, AlgHom.commutes, Algebra.smul_def, IsScalarTower.algebraMap_apply R B M,
    IsScalarTower.algebraMap_apply R B M] at this
  rw [map_mul, this]

end GlobalTheory
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.picard_torsion_trivial_of_torsors_have_sections : ∀ (B : Type) [CommRing B] (q : ℕ), 0 < q → IsUnit (q : B) →
    (∃ ζ : B, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) →
    (∀ (D : Type) [CommRing D] [Algebra B D], Module.Finite B D → Module.Projective B D →
      Module.FaithfullyFlat B D → ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D),
      Function.Bijective (Algebra.TensorProduct.productMap
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) → Nonempty (D →ₐ[B] B)) →
    ∀ c : CommRing.Pic B, c ^ q = 1 → c = 1 := by
  first | (exact @GlobalTheory.KummerStep.kummer_step) | (exact GlobalTheory.KummerStep.kummer_step) | (intros; apply GlobalTheory.KummerStep.kummer_step  <;> assumption)
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory.RegularAscent

theorem height_add_ringKrullDim_quotient_le {R : Type} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  apply _root_.GlobalTheory.IntersectionSymm.height_add_dim_quotient_le <;> assumption

end GlobalTheory.RegularAscent
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.height_eq_one_of_liesOver_height_one : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (A : Subalgebra k F) [IsFractionRing A F] (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 := by
  first | (exact @GlobalTheory.integralClosure_height_eq_one_of_liesOver) | (exact GlobalTheory.integralClosure_height_eq_one_of_liesOver) | (intros; apply GlobalTheory.integralClosure_height_eq_one_of_liesOver  <;> assumption)
end

section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

theorem _root_.GlobalTheory.T.exists_coordinate_polynomial_sub_mem_maximalIdeal_pow : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (z : Fin n → A), maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ (k : ℕ) (f : A), ∃ p ∈ Subring.closure (Set.range inc ∪ Set.range z), f - p ∈ maximalIdeal A ^ k := by
  first | exact @GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow | exact GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow | (intros; apply GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.finite_projective_span_of_integralClosure' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), (∀ y : K, y ∈ B ↔ y ∈ integralClosure A K) → Module.Finite A (integralClosure A K) → Module.Projective A (integralClosure A K) → ∀ (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Module.Finite B (Submodule.span B S) → Module.Projective B (Submodule.span B S) → Module.Finite A (Submodule.span A S) ∧ Module.Projective A (Submodule.span A S) := by
  first | (exact @GlobalTheory.finite_projective_span_of_integralClosure) | (exact GlobalTheory.finite_projective_span_of_integralClosure) | (intros; apply GlobalTheory.finite_projective_span_of_integralClosure  <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.exists_D_eq_sum_smul_D_of_mem_adjoin : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (n : ℕ) (u : Fin n → F), ∀ v ∈ Algebra.adjoin k (Set.range u), ∃ c : Fin n → F, (∀ j, c j ∈ Algebra.adjoin k (Set.range u)) ∧ D k K (algebraMap F K v) = ∑ j, algebraMap F K (c j) • D k K (algebraMap F K (u j)) := by
  first | (exact @GlobalTheory.dadj_combination) | (exact GlobalTheory.dadj_combination) | (intros; apply GlobalTheory.dadj_combination  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NzdDescent

open TensorProduct GlobalTheory.SmoothDescent

theorem model_data (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B] (b g : B) :
    ∃ (S B₁ : Type) (_ : CommRing S) (_ : IsNoetherianRing S) (_ : Algebra S A) (_ : CommRing B₁)
      (_ : Algebra S B₁) (_ : Algebra.Smooth S B₁) (e : A ⊗[S] B₁ ≃ₐ[A] B) (b₁ g₁ : B₁),
      Function.Injective (fun x : B₁ => e (1 ⊗ₜ x)) ∧ e (1 ⊗ₜ b₁) = b ∧ e (1 ⊗ₜ g₁) = g := by
  classical
  obtain ⟨A₀, B₀, _, _, h₀, hB, ⟨β⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A B
  haveI : IsNoetherianRing A₀ := isNoetherianRing_of_fg h₀
  obtain ⟨S, hS, hsub⟩ := exists_fg_subset_range_incl (C₁ := B₀) ({β b, β g} : Finset _)
  obtain ⟨b₁, hb₁⟩ := hsub (by simp : β b ∈ _)
  obtain ⟨g₁, hg₁⟩ := hsub (by simp : β g ∈ _)
  set_option synthInstance.maxHeartbeats 200000 in
   refine ⟨S, S ⊗[A₀] B₀, inferInstance, isNoetherianRing_of_fg hS, inferInstance, inferInstance,
    inferInstance, inferInstance,
    (Algebra.TensorProduct.cancelBaseChange A₀ S A A B₀).trans β.symm, b₁, g₁, ?_, ?_, ?_⟩
  · intro x y h
    simp only [AlgEquiv.trans_apply, cancel_one_tmul] at h
    exact incl_injective S (β.symm.injective h)
  · simp only [AlgEquiv.trans_apply, cancel_one_tmul]
    exact (congrArg β.symm hb₁).trans (β.symm_apply_apply b)
  · simp only [AlgEquiv.trans_apply, cancel_one_tmul]
    exact (congrArg β.symm hg₁).trans (β.symm_apply_apply g)

theorem of_model (hN : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0)) (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    (S B₁ : Type) (b g : B) [CommRing S] [IsNoetherianRing S] [Algebra S A] [CommRing B₁] [Algebra S B₁]
    [Algebra.Smooth S B₁] (e : A ⊗[S] B₁ ≃ₐ[A] B) (b₁ g₁ : B₁)
    (hinj : Function.Injective (fun x : B₁ => e (1 ⊗ₜ x))) (hb : e (1 ⊗ₜ b₁) = b) (hg : e (1 ⊗ₜ g₁) = g)
    (u : PrimeSpectrum B) (hgb : g * b = 0)
    (hmin : ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q) :
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  let ι : B₁ →+* B := e.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight : B₁ →ₐ[S] A ⊗[S] B₁).toRingHom
  have hι : ∀ x, ι x = e (1 ⊗ₜ x) := fun x => rfl
  have hιS : ∀ s : S, ι (algebraMap S B₁ s) = algebraMap A B (algebraMap S A s) := by
    intro s
    rw [hι, ← Algebra.TensorProduct.tmul_one_eq_one_tmul, ← Algebra.TensorProduct.algebraMap_apply,
      IsScalarTower.algebraMap_apply S A (A ⊗[S] B₁), AlgEquiv.commutes]
  have hgb₁ : g₁ * b₁ = 0 := by
    apply hinj
    show ι (g₁ * b₁) = ι 0
    rw [map_mul, hι, hι, hg, hb, hgb, map_zero]
  let u₁ : PrimeSpectrum B₁ := ⟨u.asIdeal.comap ι, Ideal.comap_isPrime _ _⟩
  have key := hN S B₁ b₁ g₁ u₁ hgb₁ ?_
  · obtain ⟨⟨t, ht⟩, htb⟩ := (IsLocalization.map_eq_zero_iff u₁.asIdeal.primeCompl _ b₁).mp key
    refine (IsLocalization.map_eq_zero_iff u.asIdeal.primeCompl _ b).mpr ⟨⟨ι t, ht⟩, ?_⟩
    show ι t * b = 0
    rw [← hb, ← hι, ← map_mul]
    simp only at htb
    rw [htb, map_zero]
  intro Q₁ hQ₁ hQ₁u hgQ₁
  haveI : Q₁.IsPrime := hQ₁.1.1
  let uT : Ideal (A ⊗[S] B₁) := u.asIdeal.comap e.toAlgHom.toRingHom
  haveI : uT.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨QT, hQTp, hQTu, hQT1, hQTA⟩ := GlobalTheory.T.exists_prime_le_comap_of_goingDown_tensor S A B₁ uT Q₁ (fun x hx => hQ₁u hx) (by
    apply le_antisymm
    · intro s hs
      have : algebraMap S B₁ s ∈ u₁.asIdeal := hQ₁u hs
      show e (algebraMap S (A ⊗[S] B₁) s) ∈ u.asIdeal
      rw [← (Algebra.TensorProduct.includeRight : B₁ →ₐ[S] A ⊗[S] B₁).commutes]
      exact this
    · intro s hs
      apply hQ₁.1.2
      apply Ideal.mem_map_of_mem
      show ι (algebraMap S B₁ s) ∈ u.asIdeal
      have : e (algebraMap S (A ⊗[S] B₁) s) ∈ u.asIdeal := hs
      rwa [← (Algebra.TensorProduct.includeRight : B₁ →ₐ[S] A ⊗[S] B₁).commutes] at this)
  let Q' : Ideal B := QT.comap e.symm.toAlgHom.toRingHom
  haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hQ'u : Q' ≤ u.asIdeal := by
    intro x hx
    have := hQTu hx
    simpa [uT] using this
  have hmap : (u.asIdeal.comap (algebraMap A B)).map (algebraMap A B) ≤ Q' := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have h1 : a ∈ uT.comap (algebraMap A (A ⊗[S] B₁)) := by
      show e (algebraMap A _ a) ∈ u.asIdeal
      rw [AlgEquiv.commutes]; exact ha
    rw [← hQTA] at h1
    show e.symm (algebraMap A B a) ∈ QT
    rw [AlgEquiv.commutes]; exact h1
  obtain ⟨Q, hQmin, hQQ'⟩ := Ideal.exists_minimalPrimes_le hmap
  apply hmin Q hQmin (hQQ'.trans hQ'u)
  haveI : Q.IsPrime := hQmin.1.1
  have hJ : Q₁ ≤ Q.comap ι := by
    refine hQ₁.2 ⟨Ideal.comap_isPrime _ _, ?_⟩ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro s hs
      show ι (algebraMap S B₁ s) ∈ Q
      rw [hιS]
      apply hQmin.1.2
      apply Ideal.mem_map_of_mem
      show algebraMap A B (algebraMap S A s) ∈ u.asIdeal
      rw [← hιS]; exact hs
    · intro x hx
      rw [← hQT1]
      have := hQQ' hx
      have h2 : e.symm (e (1 ⊗ₜ x)) ∈ QT := this
      rw [AlgEquiv.symm_apply_apply] at h2
      exact h2
  have := hJ hgQ₁
  rw [← hg]; exact this

theorem of_noetherian : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0) →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  intro hN A B _ _ _ _ b g u hgb hmin
  obtain ⟨S, B₁, _, _, _, _, _, _, e, b₁, g₁, hinj, hb, hg⟩ := model_data A B b g
  exact of_model hN A B S B₁ b g e b₁ g₁ hinj hb hg u hgb hmin

end GlobalTheory.NzdDescent
end

section

namespace GlobalTheory

open IsLocalRing

theorem derivation_mem_of_mem_sq {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    (δ : Derivation k A A) (q : Ideal A) {x : A} (hx : x ∈ q ^ 2) : δ x ∈ q := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact q.add_mem (q.mul_mem_right _ hm) (q.mul_mem_right _ hn)
  · intro x y hx hy
    rw [map_add (f := _)]; exact q.add_mem hx hy

theorem residue_algebraMap_eq_zero_iff_mem {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] (q : Ideal A) [q.IsPrime] [IsLocalization.AtPrime R q] (x : A) :
    residue R (algebraMap A R x) = 0 ↔ x ∈ q := by
  rw [residue_eq_zero_iff]
  conv_rhs => rw [← IsLocalization.AtPrime.under_maximalIdeal R q]
  rfl

theorem cotangent_relation_derivation {k A R : Type} [CommRing k] [CommRing A] [Algebra k A]
    (q : Ideal A) [q.IsPrime] [CommRing R] [IsLocalRing R] [Algebra A R]
    [IsLocalization.AtPrime R q]
    (δ : Derivation k A A) {κ : Type} (J : Finset κ) (g : κ → A)
    (hg : ∀ j, algebraMap A R (g j) ∈ maximalIdeal R) (c : κ → ResidueField R)
    (hrel : ∑ j ∈ J, c j • (maximalIdeal R).toCotangent ⟨_, hg j⟩ = 0) :
    ∑ j ∈ J, c j * residue R (algebraMap A R (δ (g j))) = 0 := by
  set ψ : A →+* ResidueField R := (residue R).comp (algebraMap A R) with hψdef
  have hψ : ∀ x, ψ x = 0 ↔ x ∈ q := fun x => residue_algebraMap_eq_zero_iff_mem q x
  have hgq : ∀ j, g j ∈ q := fun j => (hψ _).1 ((residue_eq_zero_iff _).2 (hg j))
  set r : κ → R := fun j => (residue_surjective (c j)).choose with hr
  have hrc : ∀ j, residue R (r j) = c j := fun j => (residue_surjective (c j)).choose_spec
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples q.primeCompl J r
  have hb' : ∀ i ∈ J, ∃ x : A, algebraMap A R x = (b : A) • r i := fun i hi => hb i hi
  choose! a ha using hb'
  have hb0 : ψ b ≠ 0 := fun h => b.2 ((hψ _).1 h)
  have hψa : ∀ j ∈ J, ψ (a j) = ψ b * c j := by
    intro j hj
    simp only [hψdef, RingHom.comp_apply, ha j hj, Algebra.smul_def, map_mul, hrc]
  set y : A := ∑ j ∈ J, a j * g j with hy
  have hyq : y ∈ q := q.sum_mem fun j _ => q.mul_mem_left _ (hgq j)

  have hT : (maximalIdeal R).toCotangent
      (∑ j ∈ J, algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R)) = 0 := by

    rw [map_sum]
    have : ∀ j ∈ J, (maximalIdeal R).toCotangent (algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R))
        = ψ b • (c j • (maximalIdeal R).toCotangent ⟨_, hg j⟩) := by
      intro j hj
      rw [map_smul, smul_smul, ← hψa j hj]
      exact (algebraMap_smul (ResidueField R) (algebraMap A R (a j)) _).symm
    rw [Finset.sum_congr rfl this, ← Finset.smul_sum, hrel, smul_zero]
  rw [Ideal.toCotangent_eq_zero] at hT
  have hcoe : ((∑ j ∈ J, algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R) : maximalIdeal R) : R)
      = algebraMap A R y := by

    simp [hy, Submodule.coe_sum, map_sum, map_mul, Algebra.smul_def]
  rw [hcoe, ← IsLocalization.AtPrime.map_eq_maximalIdeal q R, ← Ideal.map_pow,
    IsLocalization.mem_map_algebraMap_iff q.primeCompl R] at hT
  obtain ⟨⟨x, s⟩, hxs⟩ := hT
  rw [← map_mul, IsLocalization.eq_iff_exists q.primeCompl R] at hxs
  obtain ⟨t, ht⟩ := hxs
  have hz : (t : A) * (y * s) ∈ q ^ 2 := ht ▸ Ideal.mul_mem_left _ _ x.2
  have hδz := (hψ _).2 (derivation_mem_of_mem_sq δ q hz)
  have hs0 : ψ s ≠ 0 := fun h => s.2 ((hψ _).1 h)
  have ht0 : ψ t ≠ 0 := fun h => t.2 ((hψ _).1 h)
  have hy0 : ψ y = 0 := (hψ _).2 hyq
  have hδy : ψ (δ y) = 0 := by
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, hy0] at hδz
    simpa [hs0, ht0] using hδz
  have hg0 : ∀ j, ψ (g j) = 0 := fun j => (hψ _).2 (hgq j)

  rw [hy, map_sum, map_sum] at hδy
  simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, hg0, zero_mul, add_zero] at hδy
  rw [Finset.sum_congr rfl (fun j hj => by rw [hψa j hj, mul_assoc]), ← Finset.mul_sum] at hδy
  exact (mul_eq_zero.1 hδy).resolve_left hb0

end GlobalTheory

namespace GlobalTheory
open IsLocalRing

theorem bertini_cotangent_independent : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ), ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (q : Ideal A) [q.IsPrime] (R : Type) [CommRing R] [IsLocalRing R] [Algebra A R] [IsLocalization.AtPrime R q], (∃ p, f p ∉ q) → LinearIndependent (IsLocalRing.ResidueField R) (fun j : {j : Fin M // algebraMap A R (∑ p, u (j, p) • f p) ∈ IsLocalRing.maximalIdeal R} => ((IsLocalRing.maximalIdeal R).toCotangent ⟨_, j.2⟩ : IsLocalRing.CotangentSpace R)) := by
  intro k A _ _ _ _ _ ι _ f M
  obtain ⟨n, δ, ω, hD⟩ := GlobalTheory.T.exists_derivation_split_kaehlerD_smooth k A
  have hC := fun (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι) (h : i₀ ∈ J) =>
    GlobalTheory.T.bertini_general_members_no_derivative_relation k A n δ ω hD f M J i₀ p₀ h
  classical
  let Qf : Finset (Fin M) × Fin M × ι → MvPolynomial (Fin M × ι) k := fun x =>
    if h : x.2.1 ∈ x.1 then (hC x.1 x.2.1 x.2.2 h).choose else 1
  refine ⟨∏ x, Qf x, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro x _
    simp only [Qf]
    split_ifs with h
    · exact (hC _ _ _ h).choose_spec.1
    · exact one_ne_zero
  · intro u hu q _ R _ _ _ _ hp
    obtain ⟨p₀, hp₀⟩ := hp
    rw [map_prod, Finset.prod_ne_zero_iff] at hu
    rw [linearIndependent_iff']
    intro s w hw i₀ hi₀
    by_contra hne
    let ψ : A →+* ResidueField R := (residue R).comp (algebraMap A R)
    letI : Algebra k (ResidueField R) := (ψ.comp (algebraMap k A)).toAlgebra
    let φ : A →ₐ[k] ResidueField R := { ψ with commutes' := fun _ => rfl }
    let J : Finset (Fin M) := s.map (Function.Embedding.subtype _)
    let c : Fin M → ResidueField R := fun j =>
      if h : algebraMap A R (∑ p, u (j, p) • f p) ∈ maximalIdeal R then w ⟨j, h⟩ / w i₀ else 0
    have hJ : i₀.1 ∈ J := Finset.mem_map_of_mem _ hi₀
    have hx := hu (J, i₀.1, p₀) (Finset.mem_univ _)
    simp only [Qf, dif_pos hJ] at hx
    refine (hC J i₀.1 p₀ hJ).choose_spec.2 u hx (ResidueField R) φ c ?_ ?_ ?_ ?_
    · exact fun h => hp₀ ((residue_algebraMap_eq_zero_iff_mem q _).1 h)
    · show c i₀.1 = 1
      rw [show c i₀.1 = w i₀ / w i₀ from dif_pos i₀.2]
      exact div_self hne
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hi
      exact (residue_eq_zero_iff _).2 j.2
    · intro l
      have hrel : ∑ j ∈ s, (w j / w i₀) •
          (maximalIdeal R).toCotangent ⟨_, j.2⟩ = 0 := by
        simp_rw [div_eq_mul_inv, mul_comm _ (w i₀)⁻¹, mul_smul]
        rw [← Finset.smul_sum, hw, smul_zero]
      have key := cotangent_relation_derivation q (δ l) s
        (fun j => ∑ p, u (j.1, p) • f p) (fun j => j.2) (fun j => w j / w i₀) hrel
      rw [Finset.sum_map]
      convert key using 2 with j hj
      show c j.1 * φ _ = _
      rw [show c j.1 = w j / w i₀ from dif_pos j.2]
      rfl

end GlobalTheory
end

section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

theorem _root_.GlobalTheory.T.exists_solve_mvPowerSeries_matrix_identity_const : ∀ (n : ℕ) (R : Type) [CommRing R] (J : Fin n → Fin n → MvPowerSeries (Fin n) R), (∀ i j, MvPowerSeries.constantCoeff (J i j) = if i = j then 1 else 0) → ∀ b : Fin n → MvPowerSeries (Fin n) R, ∃ G : Fin n → MvPowerSeries (Fin n) R, ∀ i, ∑ j, G j * J i j = b i := by
  first | exact @GlobalTheory.powerSeries_matrix_solve | exact GlobalTheory.powerSeries_matrix_solve | (intros; apply GlobalTheory.powerSeries_matrix_solve <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.abhyankar_ramificationIdx_eq_one_alt : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    Q.ramificationIdx D = 1 := by
  first | (exact @GlobalTheory.abhyankar_ramificationIdx_eq_one) | (exact GlobalTheory.abhyankar_ramificationIdx_eq_one) | (intros; apply GlobalTheory.abhyankar_ramificationIdx_eq_one  <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.exists_local_kaehlerD_basis_smooth_subalgebra : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (d : ℕ), Module.finrank K Ω[K⁄k] = d → ∀ (P : Ideal B) [P.IsPrime], ∃ (f : B) (u : Fin d → B) (b : Module.Basis (Fin d) K Ω[K⁄k]), f ∉ P ∧ (∀ j, b j = D k K (u j : K)) ∧ ∀ (v : B) (j : Fin d), ∃ c : B, (f : K) * b.repr (D k K (v : K)) j = c := by
  first | (exact @GlobalTheory.PD.exists_local_dbasis) | (exact GlobalTheory.PD.exists_local_dbasis) | (intros; apply GlobalTheory.PD.exists_local_dbasis  <;> assumption)
end
