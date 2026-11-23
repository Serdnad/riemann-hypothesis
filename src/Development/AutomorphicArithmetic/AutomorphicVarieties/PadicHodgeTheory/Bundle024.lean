module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsHomogeneousLiftModKerPowSuccSup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNotMemMulMemIdealOfForallPrimePowSup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle068
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle017
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem sc_pi (E : Type) [Field E] (n k : ℕ) :
    ∃ π : (MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ (k + 2)) →ₐ[E] E,
      (∀ g, π (Ideal.Quotient.mk _ g) = MvPowerSeries.constantCoeff g) ∧ ∀ a, π a = 0 → IsNilpotent a := by
  let cc : MvPowerSeries (Fin n) E →ₐ[E] E :=
    { (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) E →+* E) with
      commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
  refine ⟨Ideal.Quotient.liftₐ _ cc fun g hg => (sc_max E n g).1 (Ideal.pow_le_self (by omega) hg),
    fun g => rfl, fun a ha => ?_⟩
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨k + 2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow ((sc_max E n g).2 ha) _

private theorem sc_inj {O E R : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
    [CommRing R] [Algebra O R] (I : Ideal R) (x : R →ₐ[O] O) (n : ℕ) (φ : R →ₐ[O] MvPowerSeries (Fin n) E)
    (t : Fin n → R) (c : O) (hc : c ≠ 0) (hI : I ≤ RingHom.ker φ)
    (hconst : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) (ht0 : ∀ i, x (t i) = 0)
    (ht : ∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2)
    (hspan : ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I)
    (N : ℕ) : ∀ a, φ a ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ N →
      ∃ e : O, e ≠ 0 ∧ e • a ∈ RingHom.ker x ^ N ⊔ I := by
  have hmap : ∀ k, ∀ b ∈ RingHom.ker x ^ k ⊔ I, φ b ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ k := by
    intro k
    have : RingHom.ker x ^ k ⊔ I ≤ (maximalIdeal (MvPowerSeries (Fin n) E) ^ k).comap (φ : R →+* _) := by
      refine sup_le (le_trans (Ideal.pow_right_mono (fun y hy => ?_) k) (Ideal.le_comap_pow _ k)) fun y hy => ?_
      · refine (sc_max E n (φ y)).2 ?_
        rw [hconst, show x y = 0 from hy, map_zero]
      · show φ y ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ k
        rw [show φ y = 0 from hI hy]
        exact zero_mem _
    exact fun b hb => this hb
  induction N with
  | zero => exact fun a _ => ⟨1, one_ne_zero, by simp⟩
  | succ N ih =>
    intro a ha
    obtain ⟨e, he, h1⟩ := ih a (Ideal.pow_le_pow_right (Nat.le_succ N) ha)
    obtain ⟨b, hb, i, hi, hbi⟩ := Submodule.mem_sup.1 h1
    obtain ⟨e', h, he', hh, h2⟩ := UpperTheory.exists_homogeneous_lift_mod_ker_pow_succ_sup O R I x n t ht0 hspan N b hb
    have hφb : φ b = e • φ a := by
      rw [← map_smul, ← hbi, map_add (f := _), show φ i = 0 from hI hi, add_zero]
    have h3 : MvPolynomial.aeval (fun j => φ (t j)) h ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ (N + 1) := by
      have h4 := hmap _ _ h2
      rw [map_sub, map_smul, hφb, MvPolynomial.comp_aeval_apply] at h4
      have h5 : e' • e • φ a ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ (N + 1) :=
        Submodule.smul_of_tower_mem _ _ (Submodule.smul_of_tower_mem _ _ ha)
      simpa using sub_mem h5 h4
    have h0 := UpperTheory.eq_zero_of_homogeneous_aeval_mem_maximalIdeal_pow_succ O E n _ c hc ht N h hh h3
    rw [h0, map_zero, sub_zero] at h2
    refine ⟨e' * e, mul_ne_zero he' he, ?_⟩
    rw [mul_smul, ← hbi, smul_add]
    exact add_mem h2 (Ideal.mem_sup_right (Submodule.smul_of_tower_mem _ _ hi))

private theorem sc_dim {O E R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Field E] [Algebra O E] [IsFractionRing O E]
    [CommRing R] [Algebra O R] [IsCO O R] (I : Ideal R) (x : R →ₐ[O] O) (n : ℕ)
    (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → R) (c : O) (hc : c ≠ 0) (hI : I ≤ RingHom.ker φ)
    (hconst : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) (ht0 : ∀ i, x (t i) = 0)
    (ht : ∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2)
    (hspan : ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I) :
    ringKrullDim (R ⧸ RingHom.ker φ) = (n + 1 : ℕ) := by
  have : IsDomain (MvPowerSeries (Fin n) E) := NoZeroDivisors.to_isDomain _
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have : IsCO O (R ⧸ RingHom.ker φ) :=
    co_quot O R _ (Ideal.Quotient.mkₐ O _) Ideal.Quotient.mk_surjective
  have hPx : ∀ a ∈ RingHom.ker φ, x a = 0 := fun a ha => by
    refine IsFractionRing.injective O E ?_
    rw [← hconst, show φ a = 0 from ha, map_zero, map_zero]
  obtain ⟨x', hx'⟩ : ∃ x' : (R ⧸ RingHom.ker φ) →ₐ[O] O, ∀ a, x' (Ideal.Quotient.mk _ a) = x a :=
    ⟨Ideal.Quotient.liftₐ _ x hPx, fun _ => rfl⟩
  obtain ⟨φ', hφ'⟩ : ∃ φ' : (R ⧸ RingHom.ker φ) →ₐ[O] MvPowerSeries (Fin n) E,
      ∀ a, φ' (Ideal.Quotient.mk _ a) = φ a := ⟨Ideal.Quotient.liftₐ _ φ fun _ h => h, fun _ => rfl⟩
  have h1 := UpperTheory.ringKrullDim_mvPowerSeries_fin_field O E _ x' n φ' (fun i => Ideal.Quotient.mk _ (t i)) c hc
    (fun a => by obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a; rw [hφ', hx', hconst])
    (fun i => by rw [hφ']; exact ht i)
  have h2 := UpperTheory.height_ker_section_le_of_cotangent_generators O _ x' n (fun i => Ideal.Quotient.mk _ (t i)) (fun i => by rw [hx', ht0])
    (fun a ha => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨e, o, he, h⟩ := hspan a (by rw [← hx', ha])
      refine ⟨e, o, he, ?_⟩
      have hle : RingHom.ker x ^ 2 ⊔ I ≤ (RingHom.ker x' ^ 2).comap (Ideal.Quotient.mk (RingHom.ker φ)) := by
        refine sup_le (le_trans (Ideal.pow_right_mono (fun y hy => ?_) 2) (Ideal.le_comap_pow _ 2)) fun y hy => ?_
        · exact (hx' y).trans hy
        · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (hI hy)]
          exact zero_mem _
      have h3 : Ideal.Quotient.mkₐ O (RingHom.ker φ) (e • a - ∑ i, o i • t i) ∈ RingHom.ker x' ^ 2 := hle h

      simpa only [map_sub, map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk] using h3)
  rw [UpperTheory.ringKrullDim_eq_height_ker_section_add_one O _ x', le_antisymm h2 h1]
  norm_cast

private theorem sc_end {O E R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Field E] [Algebra O E] [IsFractionRing O E]
    [CommRing R] [Algebra O R] [IsCO O R] (I : Ideal R) (x : R →ₐ[O] O) (hIx : I ≤ RingHom.ker x) (n : ℕ)
    (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → R) (c : O) (hc : c ≠ 0) (hI : I ≤ RingHom.ker φ)
    (hconst : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) (ht0 : ∀ i, x (t i) = 0)
    (ht : ∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2)
    (hspan : ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I) :
    ∃ P : Ideal R, UpperTheory.V.Loc.IsCompl P x φ ∧ I ≤ P ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a ∈ I) ∧
      (∀ Q ∈ I.radical.minimalPrimes, Q ≤ RingHom.ker x ↔ Q = P) ∧ P ∈ I.radical.minimalPrimes ∧
      ringKrullDim (R ⧸ P) = (n + 1 : ℕ) := by
  have : IsDomain (MvPowerSeries (Fin n) E) := NoZeroDivisors.to_isDomain _
  have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hinj := sc_inj I x n φ t c hc hI hconst ht0 ht hspan
  have hPx : RingHom.ker φ ≤ RingHom.ker x := fun a ha => by
    refine IsFractionRing.injective O E ?_
    rw [← hconst, show φ a = 0 from ha, map_zero, map_zero]
  obtain ⟨y, hy, hyP⟩ := UpperTheory.exists_not_mem_mul_mem_ideal_of_forall_prime_pow_sup R I (RingHom.ker x) (RingHom.ker φ) (RingHom.ker_isPrime _) hIx
    fun a ha N => by
      obtain ⟨e, he, h⟩ := hinj N a (by rw [show φ a = 0 from ha]; exact zero_mem _)
      refine ⟨algebraMap O R e, fun h' => he ?_, by rwa [← Algebra.smul_def]⟩
      simpa using h'
  have hle : ∀ Q : Ideal R, Q.IsPrime → I.radical ≤ Q → Q ≤ RingHom.ker x → RingHom.ker φ ≤ Q :=
    fun Q hQ h1 h2 a ha => (hQ.mem_or_mem (h1 (Ideal.le_radical (hyP a ha)))).resolve_left fun h => hy (h2 h)
  have hrad : I.radical ≤ RingHom.ker φ := hP.radical_le_iff.2 hI
  refine ⟨RingHom.ker φ, ⟨rfl, hconst, UpperTheory.power_series_approximation_mod_maximal O E R n φ t c hc ht, fun N a ha => ?_⟩, hI, ⟨y, hy, hyP⟩,
    fun Q hQ => ⟨fun h => ?_, fun h => h ▸ hPx⟩, ⟨⟨hP, hrad⟩, fun Q hQ h => hle Q hQ.1 hQ.2 (h.trans hPx)⟩,
    sc_dim I x n φ t c hc hI hconst ht0 ht hspan⟩
  · obtain ⟨e, he, h⟩ := hinj N a ha
    exact ⟨e, he, sup_le_sup_left hI _ h⟩
  · have h1 := hle Q hQ.1.1 hQ.1.2 h
    exact le_antisymm (hQ.2 ⟨hP, hrad⟩ h1) h1

theorem UpperTheory.V.Loc.smoothCompl :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (I : Ideal R) (x : R →ₐ[O] O), I ≤ RingHom.ker x → (∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ f' : R →ₐ[O] B', I ≤ RingHom.ker f' → (∀ a, π' (f' a) = algebraMap O E (x a)) → ∃ f : R →ₐ[O] B, I ≤ RingHom.ker f ∧ ∀ a, p (f a) = f' a) → ∃ (n : ℕ) (P : Ideal R) (φ : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P x φ ∧ I ≤ P ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a ∈ I) ∧ (∀ Q ∈ I.radical.minimalPrimes, Q ≤ RingHom.ker x ↔ Q = P) ∧ P ∈ I.radical.minimalPrimes ∧ ringKrullDim (R ⧸ P) = (n + 1 : ℕ) := by
  intro l _ O _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ R _ _ _ I x hIx H
  obtain ⟨n, D, t, c, hc, hD, hDI, ht0, htD, hspan⟩ := UpperTheory.exists_derivations_dual_to_cotangent_parameters O E R I x hIx
  obtain ⟨f₀, hf₀⟩ := sc_first x n D hD
  have : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) E)) (MvPowerSeries (Fin n) E) := by
    rw [← sc_span]; infer_instance
  have hfin : ∀ k, Module.Finite ℚ_[l] (MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ k) :=
    fun k => by
      have : Module.Finite E (MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ k) :=
        GlobalTheory.FormalIsogeny.finite_quotient_of_pow_le (N := k) (by rw [sc_span])
      exact Module.Finite.trans E _
  have hc0 : ∀ a g, Ideal.Quotient.mk _ g = f₀ a → MvPowerSeries.constantCoeff g = algebraMap O E (x a) := by
    intro a g hg
    rw [hf₀, Ideal.Quotient.eq] at hg
    have := (sc_max E n _).1 (Ideal.pow_le_self (by omega) hg)
    simpa [sub_eq_zero] using this
  obtain ⟨φ, hφI, hφ⟩ := sc_tower (maximalIdeal (MvPowerSeries (Fin n) E)) I f₀
    (fun a ha => by
      rw [RingHom.mem_ker, hf₀, show x a = 0 from hIx ha]
      simp [hDI _ a ha])
    (fun N f' h1 h2 => by
      obtain ⟨π, hπ, hn⟩ := sc_pi E n (N + 1)
      obtain ⟨π', hπ', hn'⟩ := sc_pi E n N
      have := hfin (N + 1 + 2)
      have := hfin (N + 2)
      refine H _ π hn _ π' hn' (Ideal.Quotient.factorₐ E (Ideal.pow_le_pow_right (by omega : N + 2 ≤ N + 1 + 2)))
        (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (by omega : N + 2 ≤ N + 1 + 2))) (AlgHom.ext fun b => ?_) f' h1 fun a => ?_
      · obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
        exact (hπ' g).trans (hπ g).symm
      · obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (f' a)
        rw [← hg, hπ']
        refine hc0 a g ?_
        rw [← h2, ← hg, Ideal.Quotient.factor_mk])
  obtain ⟨P, hP⟩ := sc_end I x hIx n φ t c hc hφI (fun a => hc0 a _ (hφ a)) ht0 (fun i => by
    have h := hφ (t i)
    rw [hf₀, Ideal.Quotient.eq] at h
    simpa [ht0, htD, apply_ite, Algebra.smul_def, MvPowerSeries.algebraMap_apply] using h) hspan
  exact ⟨n, P, φ, hP⟩
end

section

open UpperTheory.V.Loc UpperTheory.V.Alg IsLocalRing MvPowerSeries

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : ∃ g : σ → MvPowerSeries σ O, f = ∑ i, MvPowerSeries.X i * g i :=
  _root_.UpperTheory.Reformulated.B.MemSpanMonomial.mem_span_X f hf

private theorem mem_max {E σ : Type} [Field E] (a : MvPowerSeries σ E) :
    a ∈ maximalIdeal _ ↔ constantCoeff a = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

private theorem lin_part {E : Type} [Field E] {n : ℕ} (f : MvPowerSeries (Fin n) E)
    (hf : constantCoeff f = 0) :
    f - ∑ j, coeff (Finsupp.single j 1) f • (X j : MvPowerSeries (Fin n) E) ∈ maximalIdeal _ ^ 2 := by
  obtain ⟨g, hg⟩ := mem_span_X f hf
  have hc : ∀ j, coeff (Finsupp.single j 1) f = constantCoeff (g j) := by
    intro j

    rw [hg, map_sum, Finset.sum_eq_single j]
    · rw [MvPowerSeries.X, coeff_monomial_mul, if_pos le_rfl, one_mul, tsub_self,
        coeff_zero_eq_constantCoeff_apply]
    · intro i _ hij
      rw [MvPowerSeries.X, coeff_monomial_mul, if_neg]
      intro h
      have := h i
      simp [Finsupp.single_apply, hij.symm] at this
    · simp
  simp only [hc]
  rw [hg, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [smul_eq_C_mul, mul_comm (C _), ← mul_sub, pow_two]
  exact Ideal.mul_mem_mul ((mem_max _).2 (by simp)) ((mem_max _).2 (by simp))

private theorem inj_of_surj {A : Type} [CommRing A] [IsNoetherianRing A] (s : A →+* A)
    (hs : Function.Surjective s) : Function.Injective s := by
  let K : ℕ →o Ideal A := ⟨fun k => RingHom.ker (s ^ k), monotone_nat_of_le_succ fun k a ha => by
    rw [RingHom.mem_ker] at ha ⊢
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ha, map_zero]⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.2 (inferInstance : IsNoetherian A A) K
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have hsN : Function.Surjective (s ^ N) := by
    rw [RingHom.coe_pow]; exact hs.iterate N
  obtain ⟨b, rfl⟩ := hsN a
  have h1 : b ∈ K (N + 1) := by
    show (s ^ (N + 1)) b = 0
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ha]
  rw [← hN (N + 1) (Nat.le_succ N)] at h1
  exact h1

private theorem exists_equiv {E : Type} [Field E] {n : ℕ} (y : Fin n → MvPowerSeries (Fin n) E)
    (hy : ∀ i, constantCoeff (y i) = 0)
    (hsp : Submodule.span E (Set.range fun i j : Fin n => coeff (Finsupp.single j 1) (y i)) = ⊤) :
    ∃ s : MvPowerSeries (Fin n) E ≃ₐ[E] MvPowerSeries (Fin n) E, ∀ i, s (X i) = y i := by
  haveI : IsAdicComplete (maximalIdeal E) E := by
    rw [maximalIdeal_eq_bot]; infer_instance
  haveI := co_mvps E E (Fin n)
  obtain ⟨s, ⟨-, hs⟩, -⟩ := co_ev E E (MvPowerSeries (Fin n) E) (Fin n) (Algebra.ofId E _) y
    fun i => (mem_max _).2 (hy i)
  have hsurj : Function.Surjective s := by
    refine co_surj E _ _ s fun f hf => ?_
    set J := (maximalIdeal (MvPowerSeries (Fin n) E)).map s ⊔ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2
    have hT : ∀ v : Fin n → E, ∑ j, v j • (X j : MvPowerSeries (Fin n) E) ∈ J := by
      intro v
      have hv : v ∈ Submodule.span E (Set.range fun i j : Fin n => coeff (Finsupp.single j 1) (y i)) := by
        rw [hsp]; trivial
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨i, rfl⟩ := hv
        have h1 : y i ∈ J := Ideal.mem_sup_left (by
          rw [← hs]; exact Ideal.mem_map_of_mem s ((mem_max _).2 (by simp)))
        have h2 := Ideal.mem_sup_right (S := (maximalIdeal (MvPowerSeries (Fin n) E)).map s) (lin_part (y i) (hy i))
        simpa using J.sub_mem h1 h2
      | zero => simp
      | add a b _ _ ha hb =>
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        exact J.add_mem ha hb
      | smul c a _ ha =>
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
        rw [smul_eq_C_mul]
        exact J.mul_mem_left _ ha
    have h2 := Ideal.mem_sup_right (S := (maximalIdeal (MvPowerSeries (Fin n) E)).map s)
      (lin_part f ((mem_max _).1 hf))
    simpa using J.add_mem h2 (hT fun j => coeff (Finsupp.single j 1) f)
  exact ⟨AlgEquiv.ofBijective s ⟨inj_of_surj s.toRingHom hsurj, hsurj⟩, hs⟩

private theorem const_equiv {E σ : Type} [Field E] (s : MvPowerSeries σ E ≃ₐ[E] MvPowerSeries σ E)
    (f : MvPowerSeries σ E) : constantCoeff (s f) = constantCoeff f := by
  have h1 : f - algebraMap E _ (constantCoeff f) ∈ maximalIdeal _ :=
    (mem_max _).2 (by simp [MvPowerSeries.algebraMap_apply])
  have h2 : s (f - algebraMap E _ (constantCoeff f)) ∈ maximalIdeal _ := fun h => h1 (by
    simpa using h.map s.symm)
  rw [mem_max, map_sub, AlgEquiv.commutes] at h2
  simpa [MvPowerSeries.algebraMap_apply, sub_eq_zero] using h2

private theorem pow_equiv {E σ : Type} [Field E] (s : MvPowerSeries σ E ≃ₐ[E] MvPowerSeries σ E) (N : ℕ)
    {f : MvPowerSeries σ E} (hf : f ∈ maximalIdeal _ ^ N) : s f ∈ maximalIdeal _ ^ N := by
  have h : maximalIdeal (MvPowerSeries σ E) ≤ (maximalIdeal _).comap s := fun a ha => by
    rw [Ideal.mem_comap, mem_max, const_equiv]; exact (mem_max _).1 ha
  exact ((Ideal.pow_right_mono h N).trans (Ideal.le_comap_pow _ N)) hf

theorem UpperTheory.V.Loc.chartChange :
    ∀ {O R E : Type} [CommRing O] [CommRing R] [Algebra O R] [Field E] [Algebra O E] (n : ℕ) (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (z : Fin n → R), UpperTheory.V.Loc.IsCompl I x φ → (∀ i, x (z i) = 0) → Submodule.span E (Set.range fun i j : Fin n => MvPowerSeries.coeff (Finsupp.single j 1) (φ (z i))) = ⊤ → ∃ φ' : R →ₐ[O] MvPowerSeries (Fin n) E, UpperTheory.V.Loc.IsCompl I x φ' ∧ ∀ i, φ' (z i) = MvPowerSeries.X i := by
  intro O R E _ _ _ _ _ n I x φ z h hz hsp
  obtain ⟨s, hs⟩ := exists_equiv (fun i => φ (z i)) (fun i => by rw [h.const, hz, map_zero]) hsp
  let φ' : R →ₐ[O] MvPowerSeries (Fin n) E := ((s.symm.restrictScalars O).toAlgHom).comp φ
  have hφ : ∀ a, φ' a = s.symm (φ a) := fun _ => rfl
  refine ⟨φ', ⟨?_, fun a => ?_, fun N f => ?_, fun N a ha => ?_⟩, fun i => ?_⟩
  · rw [← h.ker]
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker, hφ, map_eq_zero_iff _ s.symm.injective]
  · rw [hφ, const_equiv, h.const]
  · obtain ⟨a, c, hc, hm⟩ := h.dense N (s f)
    refine ⟨a, c, hc, ?_⟩
    have h1 := pow_equiv s.symm N hm
    have h2 : s.symm (c • s f) = c • f := by
      rw [← algebraMap_smul E c, map_smul, AlgEquiv.symm_apply_apply, algebraMap_smul]
    rwa [map_sub, h2] at h1
  · refine h.inj N a ?_
    have h1 := pow_equiv s N ha
    rwa [hφ, AlgEquiv.apply_symm_apply] at h1
  · rw [hφ, ← hs, AlgEquiv.symm_apply_apply]
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem companion {R : Type} [CommRing R] (P : R[X]) (hP : P.Monic) (h0 : IsUnit (P.coeff 0)) :
    ∃ M : Matrix (Fin P.natDegree) (Fin P.natDegree) R, IsUnit M.det ∧
      ∀ i : Fin P.natDegree, P ∣ X ^ ((i : ℕ) + 1) - ∑ j : Fin P.natDegree, C (M i j) * X ^ (j : ℕ) := by
  classical
  let b : Basis (Fin P.natDegree) R (AdjoinRoot P) := (AdjoinRoot.powerBasis' hP).basis
  have hb : ∀ i : Fin P.natDegree, b i = AdjoinRoot.root P ^ (i : ℕ) := fun i =>
    (AdjoinRoot.powerBasis' hP).basis_eq_pow i
  have hr : IsUnit (AdjoinRoot.root P) := by
    have h1 : AdjoinRoot.mk P (X * divX P + C (P.coeff 0)) = 0 := by
      rw [X_mul_divX_add]; exact AdjoinRoot.mk_self
    rw [map_add (f := _), map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h1
    have h2 : IsUnit (AdjoinRoot.root P * AdjoinRoot.mk P (divX P)) := by
      rw [eq_neg_of_add_eq_zero_left h1]
      exact (h0.map (AdjoinRoot.of P)).neg
    exact isUnit_of_mul_isUnit_left h2
  refine ⟨(Algebra.leftMulMatrix b (AdjoinRoot.root P)).transpose, ?_, fun i => ?_⟩
  · rw [Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]
    exact hr.map _
  · rw [← AdjoinRoot.mk_eq_mk]
    have h := b.sum_repr (AdjoinRoot.root P * b i)

    simp only [map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, Matrix.transpose_apply,
    Algebra.leftMulMatrix_eq_repr_mul]
    rw [pow_succ', ← hb, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h, Algebra.smul_def, hb j]
    rfl

theorem UpperTheory.inertia_fixes_of_frobenius_annihilated_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (P : ℤ_[l][X]), P.Monic → IsUnit (P.coeff 0) → ∀ x : Bcr l, aeval ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) (P.map (algebraMap ℤ_[l] ℚ_[l])) x = 0 → (∀ i : ℕ, (PP l).ιB (((PP l).φB)^[i] x) ∈ ((PP l).PD (botExt l)).Fil 0) → ∀ g ∈ Iq l, (PP l).actQ g x = x := by
  intro l _ P hP h0 x hx hF g hg
  classical
  rcases Nat.eq_zero_or_pos P.natDegree with hd | hd
  · rw [hP.natDegree_eq_zero.1 hd, Polynomial.map_one, map_one, Module.End.one_apply] at hx
    rw [hx, map_zero]
  obtain ⟨M, hM, hdiv⟩ := companion P hP h0
  obtain ⟨N, N', hNN, -, hN', hφ, hI⟩ := UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace M hM
  let V : Fin P.natDegree → Bcr l := fun i => ((PP l).φB)^[i] x
  have hpow : ∀ k : ℕ, (((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ k) x = ((PP l).φB)^[k] x :=
    fun k => by rw [Module.End.pow_apply]; rfl
  have hV : ∀ i, (PP l).φB (V i) =
      ((M.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l]))).mulVec V) i := fun i => by
    obtain ⟨Q, hQ⟩ := hdiv i
    have h1 := congrArg (fun p : ℤ_[l][X] => aeval ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l))
      (p.map (algebraMap ℤ_[l] ℚ_[l])) x) hQ
    rw [mul_comm P Q, Polynomial.map_mul, map_mul, Module.End.mul_apply, hx, map_zero] at h1

    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sum, Polynomial.map_mul, map_X, map_C,
    map_sub, map_sum, map_mul, map_pow, aeval_X, aeval_C, LinearMap.sub_apply, LinearMap.sum_apply,
    Module.End.mul_apply, hpow, Module.algebraMap_end_apply] at h1
    rw [Function.iterate_succ_apply', sub_eq_zero] at h1
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Algebra.smul_def]
    rfl
  have hN'N : N' * N = 1 := mul_eq_one_comm.1 hNN
  let Y : Fin P.natDegree → Bcr l := N'.mulVec V
  have hVY : N.mulVec Y = V := by
    simp only [Y, Matrix.mulVec_mulVec, hNN, Matrix.one_mulVec]
  have hφY : ∀ i, (PP l).φB (Y i) = Y i := fun i => by
    have h1 : (PP l).φB (Y i) = ((N'.map (PP l).φB).mulVec ((PP l).φB ∘ V)) i :=
      RingHom.map_mulVec ((PP l).φB : Bcr l →+* Bcr l) N' V i
    have h2 : (PP l).φB ∘ V = (M.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l]))).mulVec V :=
      funext hV
    have h3 : N'.map (PP l).φB * N.map (PP l).φB = 1 := by
      have := congrArg ((PP l).φB : Bcr l →+* Bcr l).mapMatrix hN'N
      rw [map_mul, map_one] at this
      exact this
    rw [h1, h2, ← hVY, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← hφ, h3,
      Matrix.one_mulVec]
  have hYF : ∀ i, (PP l).ιB (Y i) ∈ ((PP l).PD (botExt l)).Fil 0 := fun i => by
    have h1 : Y i = ∑ j, N' i j * V j := rfl

    rw [h1, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_mul]
    simpa using ((PP l).PD (botExt l)).Fil_mul 0 0 _ _ (hN' i j) (hF j)
  have hgY : (PP l).actQ g ∘ Y = Y := funext fun i => by
    obtain ⟨c, hc⟩ := ((PP l).PD (botExt l)).fund (Y i) (by rw [(PP l).PD_φ]; exact hφY i)
      (by rw [(PP l).PD_ι]; exact hYF i)
    change (PP l).actQ g (Y i) = Y i
    rw [← hc, AlgEquiv.commutes]
  have h1 : (PP l).actQ g (N.mulVec Y ⟨0, hd⟩) =
      ((N.map ((PP l).actQ g)).mulVec ((PP l).actQ g ∘ Y)) ⟨0, hd⟩ :=
    RingHom.map_mulVec (((PP l).actQ g : Bcr l ≃ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l) N Y _
  rw [hI g hg, hgY, hVY] at h1
  exact h1
end
