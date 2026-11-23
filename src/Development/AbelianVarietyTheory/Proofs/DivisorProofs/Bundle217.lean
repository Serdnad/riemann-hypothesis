module

public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle088
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle091
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle096
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle092
public import Mathlib.RingTheory.Invariant.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle084
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.Ideal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

def sqZeroInterp {R B S : Type} [CommRing R] [CommRing B] [CommRing S] [Algebra R B]
    [Algebra R S] (J : Ideal S) (hJ : J ^ 2 = ⊥) (α β : B →ₐ[R] S) (h : ∀ x, β x - α x ∈ J)
    (c : S) : B →ₐ[R] S where
  toFun x := α x + c * (β x - α x)
  map_one' := by simp
  map_mul' x y := by
    have hxy : (β x - α x) * (β y - α y) = 0 := by
      have hm := Ideal.mul_mem_mul (h x) (h y)
      rw [← pow_two, hJ] at hm
      simpa using hm
    simp only [map_mul]
    linear_combination (c - c ^ 2) * hxy
  map_zero' := by simp
  map_add' x y := by simp only [map_add (f := _)]; ring
  commutes' r := by simp

@[simp] theorem sqZeroInterp_apply {R B S : Type} [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] (J : Ideal S) (hJ : J ^ 2 = ⊥) (α β : B →ₐ[R] S)
    (h : ∀ x, β x - α x ∈ J) (c : S) (x : B) :
    sqZeroInterp J hJ α β h c x = α x + c * (β x - α x) := rfl

theorem exists_sqZero_extend_base (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S]
    [Algebra R' A] [Algebra R' S]
    [hfp : Algebra.FinitePresentation R' A] (J : Ideal S) (hJ : J ^ 2 = ⊥) (g : S)
    (φ : A →ₐ[R'] S) (ψ : A →ₐ[R'] Localization.Away g)
    (hψ : ∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈
      J.map (algebraMap S (Localization.Away g))) :
    ∃ N₀ : ℕ, ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N₀ *
          (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  obtain ⟨n, π, hπ, hker⟩ := hfp.out
  have hJg : (J.map (algebraMap S (Localization.Away g))) ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  have hy : ∀ i : Fin n, ∃ k : ℕ, ∃ y ∈ J, algebraMap S (Localization.Away g) y =
      algebraMap S (Localization.Away g) g ^ k * (ψ (π (MvPolynomial.X i)) -
        algebraMap S (Localization.Away g) (φ (π (MvPolynomial.X i)))) := by
    intro i
    obtain ⟨⟨⟨j, hj⟩, ⟨m, ⟨k, rfl⟩⟩⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Submonoid.powers g) (Localization.Away g)).1 (hψ (π (MvPolynomial.X i)))
    refine ⟨k, j, hj, ?_⟩
    simp only [map_pow] at e
    rw [← e]; ring
  choose k y hyJ hyeq using hy
  set M := Finset.univ.sup k with hM
  set y' : Fin n → S := fun i => g ^ (M - k i) * y i with hy'
  have hy'J : ∀ i, y' i ∈ J := fun i => J.mul_mem_left _ (hyJ i)
  have hy'eq : ∀ i, algebraMap S (Localization.Away g) (y' i) =
      algebraMap S (Localization.Away g) g ^ M * (ψ (π (MvPolynomial.X i)) -
        algebraMap S (Localization.Away g) (φ (π (MvPolynomial.X i)))) := by
    intro i
    have hk : k i ≤ M := Finset.le_sup (Finset.mem_univ i)
    simp only [y', map_mul, map_pow, hyeq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  set α₀ : MvPolynomial (Fin n) R' →ₐ[R'] S := φ.comp π with hα₀
  set β₀ : MvPolynomial (Fin n) R' →ₐ[R'] S :=
    MvPolynomial.aeval (fun i => φ (π (MvPolynomial.X i)) + y' i) with hβ₀
  have hβα : ∀ p, β₀ p - α₀ p ∈ J := by
    intro p
    rw [← Ideal.Quotient.eq]
    have e : (Ideal.Quotient.mkₐ R' J).comp β₀ = (Ideal.Quotient.mkₐ R' J).comp α₀ := by
      apply MvPolynomial.algHom_ext; intro i
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, β₀, α₀, MvPolynomial.aeval_X]
      rw [Ideal.Quotient.eq]; simpa using hy'J i
    exact DFunLike.congr_fun e p
  have hloc : ∀ p, algebraMap S (Localization.Away g) (β₀ p) =
      algebraMap S (Localization.Away g) (α₀ p) + algebraMap S (Localization.Away g) g ^ M *
        (ψ (π p) - algebraMap S (Localization.Away g) (α₀ p)) := by
    intro p
    have e : (IsScalarTower.toAlgHom R' S (Localization.Away g)).comp β₀ =
        sqZeroInterp _ hJg ((IsScalarTower.toAlgHom R' S (Localization.Away g)).comp α₀)
          (ψ.comp π) (fun q => hψ (π q)) (algebraMap S (Localization.Away g) g ^ M) := by
      apply MvPolynomial.algHom_ext; intro i
      simp only [AlgHom.comp_apply, sqZeroInterp_apply, IsScalarTower.coe_toAlgHom', β₀, α₀,
        MvPolynomial.aeval_X, map_add, hy'eq]
      rfl
    exact DFunLike.congr_fun e p

  obtain ⟨s, hs⟩ := hker
  have hrel : ∀ r ∈ s, ∃ K : ℕ, g ^ K * (β₀ r - α₀ r) = 0 := by
    intro r hr
    have hrk : r ∈ RingHom.ker π.toRingHom := hs ▸ Ideal.subset_span hr
    have hπr : π r = 0 := hrk
    have hz : algebraMap S (Localization.Away g) (β₀ r - α₀ r) = 0 := by
      rw [map_sub, hloc]; simp [α₀, hπr]
    obtain ⟨⟨m, ⟨K, rfl⟩⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).1 hz
    exact ⟨K, hm⟩
  choose! Kf hKf using hrel
  set K := s.sup Kf with hK
  set θ := sqZeroInterp J hJ α₀ β₀ hβα (g ^ K) with hθ
  have hθker : ∀ r ∈ RingHom.ker π.toRingHom, θ r = 0 := by
    intro r hr
    rw [← hs] at hr
    have hle : Ideal.span (s : Set (MvPolynomial (Fin n) R')) ≤ RingHom.ker θ := by
      rw [Ideal.span_le]
      intro r hr
      have hrk : r ∈ RingHom.ker π.toRingHom := hs ▸ Ideal.subset_span hr
      have hπr : π r = 0 := hrk
      have hle' : Kf r ≤ K := Finset.le_sup hr
      show θ r = 0
      rw [hθ, sqZeroInterp_apply]
      have : α₀ r = 0 := by simp [α₀, hπr]
      have h2 := hKf r hr
      rw [this, sub_zero] at h2
      rw [this, sub_zero, zero_add, ← Nat.sub_add_cancel hle', pow_add, mul_assoc, h2, mul_zero]
    exact hle hr
  let χ₀ : A →ₐ[R'] S := (Ideal.Quotient.liftₐ (RingHom.ker π.toRingHom) θ hθker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  have hχ₀ : ∀ p, χ₀ (π p) = θ p := by
    intro p
    have : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show Ideal.Quotient.liftₐ _ θ hθker ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π p)) = θ p
    rw [this]
    rfl
  refine ⟨K + M, χ₀, ?_, ?_⟩
  · intro x
    obtain ⟨p, rfl⟩ := hπ x
    rw [hχ₀, hθ, sqZeroInterp_apply]
    have : φ (π p) = α₀ p := rfl
    rw [this, add_sub_cancel_left]
    exact J.mul_mem_left _ (hβα p)
  · intro x
    obtain ⟨p, rfl⟩ := hπ x
    rw [hχ₀, hθ, sqZeroInterp_apply]
    have : φ (π p) = α₀ p := rfl
    rw [this, map_add (f := _), map_mul, map_sub, hloc, map_pow, pow_add]
    ring

theorem exists_sqZero_extend_pow : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FinitePresentation R' A] (J : Ideal S), J ^ 2 = ⊥ → ∀ (g : S) (φ : A →ₐ[R'] S)
    (ψ : A →ₐ[R'] Localization.Away g),
    (∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈ J.map (algebraMap S (Localization.Away g))) →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N * (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  intro R' A S _ _ _ _ _ _ J hJ g φ ψ hψ
  obtain ⟨N₀, χ₀, h1, h2⟩ := exists_sqZero_extend_base R' A S J hJ g φ ψ hψ
  refine ⟨N₀, fun N hN => ⟨sqZeroInterp J hJ φ χ₀ h1 (g ^ (N - N₀)), ?_, ?_⟩⟩
  · intro x
    rw [sqZeroInterp_apply, add_sub_cancel_left]
    exact J.mul_mem_left _ (h1 x)
  · intro x
    rw [sqZeroInterp_apply, map_add (f := _), map_mul, map_sub, h2, map_pow, add_sub_cancel_left,
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel hN]

end GlobalTheory.SecGlue
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem units_localization_descend_away (A : Type) [CommRing A] (M : Submonoid A)
    (u : (Localization M)ˣ) :
    ∃ m ∈ M, ∃ v : (Localization.Away m)ˣ, ∀ φ : Localization.Away m →+* Localization M,
      φ.comp (algebraMap A _) = algebraMap A _ → Units.map φ.toMonoidHom v = u := by
  obtain ⟨⟨a, m₁⟩, ha⟩ := IsLocalization.mk'_surjective M (u : Localization M)
  obtain ⟨⟨b, m₂⟩, hb⟩ := IsLocalization.mk'_surjective M ((u⁻¹ : (Localization M)ˣ) : Localization M)
  simp only at ha hb
  have hprod : IsLocalization.mk' (Localization M) (a * b) (m₁ * m₂) = 1 := by
    rw [IsLocalization.mk'_mul, ha, hb]; simp
  have h1 : algebraMap A (Localization M) (a * b) = algebraMap A (Localization M) ((m₁ * m₂ : M) : A) := by
    have := IsLocalization.mk'_spec (Localization M) (a * b) (m₁ * m₂)
    rw [hprod, one_mul] at this
    exact this.symm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).1 h1
  set m : A := (m₁ : A) * m₂ * c with hm
  have hmM : m ∈ M := M.mul_mem (M.mul_mem m₁.2 m₂.2) c.2
  have hc' : (c : A) * (a * b) = (c : A) * ((m₁ : A) * m₂) := by
    simpa [Submonoid.coe_mul] using hc
  let s := IsLocalization.Away.invSelf (S := Localization.Away m) m
  have hs : algebraMap A (Localization.Away m) m * s = 1 := IsLocalization.Away.mul_invSelf m
  let x : Localization.Away m := algebraMap A _ (a * (m₂ * c)) * s
  let y : Localization.Away m := algebraMap A _ (b * (m₁ * c)) * s
  have hxy : x * y = 1 := by
    have e : a * (m₂ * c) * (b * (m₁ * c)) = m * m := by
      rw [hm]; linear_combination ((m₁ : A) * m₂ * c) * hc'
    calc x * y = algebraMap A _ (a * (m₂ * c) * (b * (m₁ * c))) * s * s := by
          simp only [x, y, map_mul]; ring
      _ = (algebraMap A (Localization.Away m) m * s) * (algebraMap A (Localization.Away m) m * s) := by
          rw [e, map_mul]; ring
      _ = 1 := by rw [hs, one_mul]
  refine ⟨m, hmM, ⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
  intro φ hφ
  have hφa : ∀ r : A, φ (algebraMap A _ r) = algebraMap A (Localization M) r := fun r =>
    congrArg (fun f : A →+* Localization M => f r) hφ
  apply Units.ext
  show φ x = (u : Localization M)
  have hu : (u : Localization M) * algebraMap A _ (m₁ : A) = algebraMap A _ a := by
    rw [← ha]; exact IsLocalization.mk'_spec _ _ _
  have hφs : algebraMap A (Localization M) m * φ s = 1 := by
    rw [← hφa, ← map_mul, hs, map_one]
  have hx : φ x * algebraMap A (Localization M) (m₁ : A) = algebraMap A _ a := by
    have : φ x * algebraMap A (Localization M) (m₁ : A)
        = algebraMap A (Localization M) a * (algebraMap A (Localization M) m * φ s) := by
      simp only [x, map_mul, hφa, hm]; ring
    rw [this, hφs, mul_one]
  have hunit : IsUnit (algebraMap A (Localization M) (m₁ : A)) := IsLocalization.map_units _ m₁
  exact hunit.mul_left_inj.1 (hx.trans hu.symm)

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.linIndep_intBilinForm_charZero_combination_eq_zero : ∀ {X : Type} [AddCommGroup X] {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ X) (k : Type) [Field k] [CharZero k] (a : Fin m → k), LinearIndependent ℤ gam → (∀ y z, ∑ i, a i * (gam i y z : k) = 0) → a = 0 := by
  first | exact @GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero | exact GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero | (intros; apply GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_invariant_derivation_of_counital_comul : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∀ l : A →ₗ[k] k, (∀ a b, l (a * b) = ε a * l b + ε b * l a) → ∃ D : Derivation k A A, ∀ a, ε (D a) = l a := by
  first | exact @GlobalTheory.invariant_derivation_exists | exact GlobalTheory.invariant_derivation_exists | (intros; apply GlobalTheory.invariant_derivation_exists <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.localFactor_at_augmentation_counital_comul : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ e : A, ε e = 1 ∧ IsIdempotentElem e ∧ ∃ (ε' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] k) (Δ' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] (A ⧸ Ideal.span {1 - e}) ⊗[k] (A ⧸ Ideal.span {1 - e})), ((∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.lid k (A ⧸ Ideal.span {1 - e}) (LinearMap.rTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a) ∧ (∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.rid k (A ⧸ Ideal.span {1 - e}) (LinearMap.lTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a)) ∧ IsNilpotent (RingHom.ker ε') := by
  first | exact @GlobalTheory.localFactor_counital_descends | exact GlobalTheory.localFactor_counital_descends | (intros; apply GlobalTheory.localFactor_counital_descends <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.divisionAlgebra_order_no_small_lattice : ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (O : Type) [Ring O] (ι : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective ι → Submodule.span ℚ (Set.range ι) = ⊤ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : O →+* Module.End ℤ X), Module.finrank ℤ X < Module.finrank ℚ B → Module.finrank ℤ X = 0 := by
  first | exact @GlobalTheory.divAlg_order_no_small_lattice | exact GlobalTheory.divAlg_order_no_small_lattice | (intros; apply GlobalTheory.divAlg_order_no_small_lattice <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_injective_values_on_finrank_family : ∀ (C V Γ : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ), (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u = ν v → ∃ c : C, u - c • v = 0 ∨ ν u < ν (u - c • v)) → ∀ (F : Submodule C V) [Module.Finite C F], ∃ f : Fin (Module.finrank C F) → V, (∀ i, f i ∈ F ∧ f i ≠ 0) ∧ Function.Injective (fun i => ν (f i)) := by
  first | exact @GlobalTheory.finrank_le_card_values | exact GlobalTheory.finrank_le_card_values | (intros; apply GlobalTheory.finrank_le_card_values <;> assumption)
end

section

open scoped TensorProduct
universe u

theorem _root_.GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq : ∀ (k : Type) [Field k] (C : Type) [CommRing C] (M : Type u) [AddCommGroup M] [Module k M] [Module (k ⊗[ℤ] C) M] [IsScalarTower k (k ⊗[ℤ] C) M] [FiniteDimensional k M] (χ : C →+* k) (e : k ⊗[ℤ] C), IsIdempotentElem e → (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) e = 1 → (∀ a, (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) a = 0 → IsNilpotent (e * a)) → ∀ m : M, m ∈ (⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c)) ↔ e • m = m := by
  first | (exact @GlobalTheory.weightSpace_iff_idempotent_fixed) | (exact GlobalTheory.weightSpace_iff_idempotent_fixed) | (intros; apply GlobalTheory.weightSpace_iff_idempotent_fixed  <;> assumption)
end

section

open scoped TensorProduct
universe u

theorem _root_.GlobalTheory.T.exists_idempotent_local_of_character : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k), ∃ e : A, IsIdempotentElem e ∧ φ e = 1 ∧ ∀ a, φ a = 0 → IsNilpotent (e * a) := by
  first | (exact @GlobalTheory.exists_idem_local_of_character) | (exact GlobalTheory.exists_idem_local_of_character) | (intros; apply GlobalTheory.exists_idem_local_of_character <;> assumption)
end

section

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem finrank_le_card_mul_finrank_eigenspace_le :
    ∀ (H K R : Type) [Group H] [Fintype H] [DecidableEq H] [Field K] [CommRing R] [Algebra K R]
      (st : H → R →ₐ[K] R), (∀ x, st 1 x = x) → (∀ h h' x, st (h * h') x = st h' (st h x)) →
      ∀ (χ : H →* Kˣ) (u : R),
      (Matrix.of fun h g : H => st (h * g) u).det ∈ nonZeroDivisors R →
      ∀ (Vm V Vp N : Submodule K R) [FiniteDimensional K Vm] [FiniteDimensional K V]
        [FiniteDimensional K Vp], (∀ h, ∀ x ∈ V, st h x ∈ V) →
      (∀ h, ∀ x ∈ Vm, x * st h u ∈ V) → (∀ h, ∀ x ∈ V, x * st h u ∈ Vp) →
      (∀ x, x ∈ N ↔ x ∈ V ∧ ∀ h, st h x = ((χ h : Kˣ) : K) • x) →
      Module.finrank K Vm ≤ Fintype.card H * Module.finrank K N ∧
        Fintype.card H * Module.finrank K N ≤ Module.finrank K Vp := by
  intro H K R _ _ _ _ _ _ st h1 hmul χ u hdet Vm V Vp N _ _ _ hV hm hp hN
  obtain ⟨hTr, hPhi, hPsi⟩ := GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet H K R st h1 hmul χ u hdet
  have hNV : N ≤ V := fun x hx => ((hN x).1 hx).1
  have : FiniteDimensional K N := Submodule.finiteDimensional_of_le hNV
  have hrk : Module.finrank K (H → N) = Fintype.card H * Module.finrank K N := by
    rw [Module.finrank_pi_fintype]
    simp
  rw [← hrk]
  constructor
  · have hmem : ∀ (f : Vm) (h : H),
        ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g ((f : R) * st h u) ∈ N := fun f h =>
      (hN _).2 ⟨V.sum_mem fun g _ => V.smul_mem _ (hV g _ (hm h _ f.2)), fun g => hTr _ g⟩
    let Φ : Vm →ₗ[K] (H → N) :=
      { toFun := fun f h => ⟨_, hmem f h⟩
        map_add' := fun f f' => by
          funext h
          apply Subtype.ext
          simp only [Submodule.coe_add, add_mul, map_add (f := _), smul_add, Finset.sum_add_distrib,
            Pi.add_apply]
        map_smul' := fun c f => by
          funext h
          apply Subtype.ext
          simp only [Submodule.coe_smul, smul_mul_assoc, map_smul, Pi.smul_apply,
            RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun g _ => smul_comm _ _ _ }
    refine LinearMap.finrank_le_finrank_of_injective (f := Φ) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    apply Subtype.ext
    exact hPhi f fun h => congrArg Subtype.val (congrFun hf h)
  · have hmem : ∀ F : H → N, ∑ h, (F h : R) * st h u ∈ Vp := fun F =>
      Vp.sum_mem fun h _ => hp h _ (hNV (F h).2)
    let Ψ : (H → N) →ₗ[K] Vp :=
      { toFun := fun F => ⟨_, hmem F⟩
        map_add' := fun F F' => by
          apply Subtype.ext
          simp only [Submodule.coe_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]
        map_smul' := fun c F => by
          apply Subtype.ext
          simp only [Submodule.coe_smul, smul_mul_assoc, Pi.smul_apply,
            RingHom.id_apply, Finset.smul_sum] }
    refine LinearMap.finrank_le_finrank_of_injective (f := Ψ) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro F hF
    have := hPsi (fun h => (F h : R)) (fun h g => ((hN _).1 (F h).2).2 g)
      (congrArg Subtype.val hF)
    funext h
    exact Subtype.ext (congrFun this h)

end GlobalTheory
end

section

open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_approx_unit_padic_tensor : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ), ∃ (b : E) (s : ℚ_[ℓ] ⊗[ℚ] E), IsIntegral ℤ_[ℓ] s ∧ (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = (z : ℚ_[ℓ] ⊗[ℚ] E) * (1 + (ℓ : ℚ_[ℓ] ⊗[ℚ] E) * s) := by
  first | (exact @GlobalTheory.PadicTensorApprox.exists_approx_unit) | (exact GlobalTheory.PadicTensorApprox.exists_approx_unit) | (intros; apply GlobalTheory.PadicTensorApprox.exists_approx_unit  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_finite_extension_degree_dvd_card_invariants : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G], Function.Injective (algebraMap A B) → ∀ (k : Type) [Field k] [CharZero k] (ev : A →+* k), ∃ (K' : Type) (_ : Field K') (_ : Algebra k K') (β : B →+* K'), FiniteDimensional k K' ∧ Module.finrank k K' ∣ Nat.card G ∧ β.comp (algebraMap A B) = (algebraMap k K').comp ev := by
  first | exact @GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd | exact GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd | (intros; apply GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd <;> assumption)
end
