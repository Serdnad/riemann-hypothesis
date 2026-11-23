module

public import Mathlib.RingTheory.LaurentSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle134
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle135
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle136
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open PowerSeries

theorem _root_.GlobalTheory.T.exists_unit_matrix_adapted_to_flag : ∀ (F : Type) [Field F] (n R : ℕ) (W : Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)), Monotone W → ∃ g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ, ∀ (k : Fin (R + 1)) (j : Fin n), (j : ℕ) < Module.finrank (LaurentSeries F) (W k) → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W k := by
  first | exact @GlobalTheory.LaurentFlagBasis.adapted_integral_basis | exact GlobalTheory.LaurentFlagBasis.adapted_integral_basis | (intros; apply GlobalTheory.LaurentFlagBasis.adapted_integral_basis <;> assumption)
end

section

open PowerSeries

theorem _root_.GlobalTheory.T.diagonal_entry_of_semilinear_mod_subspace_alt : ∀ (F : Type) [Field F] (n : ℕ) (θ : PowerSeries F →+* PowerSeries F) (A : Matrix (Fin n) (Fin n) (PowerSeries F)) (W' W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (f' e' f e : Fin n → PowerSeries F) (w' w : (PowerSeries F)ˣ) (k' k m : ℤ) (d : PowerSeries F) (α : LaurentSeries F), ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 → (∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((A.mulVec (fun c => θ (y c)) a : PowerSeries F) : LaurentSeries F)) ∈ W) → (fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((f a : PowerSeries F) : LaurentSeries F)) - (((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k) • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∉ W → (fun a => ((A.mulVec (fun c => θ (f' c)) a : PowerSeries F) : LaurentSeries F)) - ((d : PowerSeries F) : LaurentSeries F) • (fun a => ((f a : PowerSeries F) : LaurentSeries F)) ∈ W → (((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m) • (fun a => ((A.mulVec (fun c => θ (e' c)) a : PowerSeries F) : LaurentSeries F)) - α • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k' * α = ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m := by
  first | exact @GlobalTheory.diagonal_entry_of_semilinear_mod_subspace | exact GlobalTheory.diagonal_entry_of_semilinear_mod_subspace | (intros; apply GlobalTheory.diagonal_entry_of_semilinear_mod_subspace <;> assumption)
end

section

open PowerSeries

theorem _root_.GlobalTheory.T.laurentSeries_adapted_basis_coords_vanish_beyond_finrank : ∀ (F : Type) [Field F] (n : ℕ) (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ), (∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W) → ∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W → ∀ a : Fin n, Module.finrank (LaurentSeries F) W ≤ (a : ℕ) → (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 := by
  first | exact @GlobalTheory.adapted_coords_vanish_stmt | exact GlobalTheory.adapted_coords_vanish_stmt | (intros; apply GlobalTheory.adapted_coords_vanish_stmt <;> assumption)
end

section


theorem _root_.GlobalTheory.T.length_ker_coker_lsmul_quotient_span_swap : ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  first | exact @GlobalTheory.kernel_cokernel_length_swap | exact GlobalTheory.kernel_cokernel_length_swap | (intros; apply GlobalTheory.kernel_cokernel_length_swap <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory

theorem exists_prime_not_mem_forall_gt_eq_maximalIdeal (C : Type) [CommRing C] [IsDomain C]
    [IsLocalRing C] [IsNoetherianRing C] (x : C) (hx : x ≠ 0) (hxm : x ∈ maximalIdeal C) :
    ∃ q : Ideal C, q.IsPrime ∧ x ∉ q ∧ ∀ P : Ideal C, P.IsPrime → q < P → P = maximalIdeal C := by
  classical

  have hnil : ¬ IsNilpotent x := fun h => hx (IsNilpotent.eq_zero h)
  haveI : Nontrivial (Localization.Away x) :=
    (IsLocalization.injective (Localization.Away x)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx)).nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Localization.Away x)
  set q : Ideal C := M.comap (algebraMap C (Localization.Away x)) with hqdef
  have hMp : M.IsPrime := hM.isPrime
  have hqd := (IsLocalization.isPrime_iff_isPrime_disjoint (Submonoid.powers x)
    (Localization.Away x) M).mp hMp
  have hqp : q.IsPrime := hqd.1
  have hxq : x ∉ q := fun h =>
    Set.disjoint_left.mp hqd.2 (Submonoid.mem_powers x) h

  have habove : ∀ P : Ideal C, P.IsPrime → q < P → x ∈ P := by
    intro P hP hlt
    by_contra hxP
    have hdisj : Disjoint (Submonoid.powers x : Set C) P := by
      rw [Set.disjoint_left]
      rintro _ ⟨n, rfl⟩ h
      exact hxP (hP.mem_of_pow_mem n h)
    have hPL := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x)
      (Localization.Away x) P hP hdisj
    have hcomap := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x)
      (Localization.Away x) hP hdisj
    have hMle : M ≤ P.map (algebraMap C (Localization.Away x)) := by
      rw [← IsLocalization.map_under (Submonoid.powers x) (Localization.Away x) M]
      exact Ideal.map_mono hlt.le
    have heq := hM.eq_of_le hPL.ne_top hMle
    have : q = P := by rw [hqdef, heq]; exact hcomap
    exact hlt.ne this
  refine ⟨q, hqp, hxq, fun P hP hlt => ?_⟩

  set f := Ideal.Quotient.mk q with hfdef
  have hsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = q := Ideal.mk_ker
  haveI : IsDomain (C ⧸ q) := Ideal.Quotient.isDomain q
  set m' : Ideal (C ⧸ q) := (maximalIdeal C).map f with hm'
  have hqm : q ≤ maximalIdeal C := le_maximalIdeal hqp.ne_top
  have hm'p : m'.IsPrime := Ideal.map_isPrime_of_surjective hsurj (hker.symm ▸ hqm)
  have hx0 : f x ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hxq
  have hht : m'.height ≤ 1 := by
    refine height_le_one_of_forall_mem m' hx0 ?_
    intro p' hp' hp'0 _
    have hcp : (p'.comap f).IsPrime := Ideal.comap_isPrime f p'
    have hqc : q < p'.comap f := by
      refine lt_of_le_of_ne ?_ ?_
      · intro a ha
        simp [Ideal.mem_comap, hfdef, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      · intro e
        apply hp'0
        rw [← Ideal.map_comap_of_surjective f hsurj p', ← e]
        exact (Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge
    exact habove _ hcp hqc
  have hPp' : (P.map f).IsPrime := Ideal.map_isPrime_of_surjective hsurj (hker.symm ▸ hlt.le)
  have hP0 : P.map f ≠ ⊥ := by
    intro e
    rw [Ideal.map_eq_bot_iff_le_ker, hker] at e
    exact hlt.ne (le_antisymm hlt.le e)
  have hPm : P.map f ≤ m' := Ideal.map_mono (le_maximalIdeal hP.ne_top)
  have hPeq : P.map f = m' := by
    by_contra hne
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hP0)
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hPm hne)
    have h3 : (⊥ : Ideal (C ⧸ q)).height + 1 + 1 ≤ 1 := (add_le_add h1 le_rfl).trans (h2.trans hht)
    simp at h3
    exact absurd h3 (by decide)
  have hPc : P = (P.map f).comap f := by
    rw [Ideal.comap_map_of_surjective' f hsurj, hker, sup_eq_left.mpr hlt.le]
  have hmc : maximalIdeal C = m'.comap f := by
    rw [hm', Ideal.comap_map_of_surjective' f hsurj, hker, sup_eq_left.mpr hqm]
  rw [hPc, hPeq, ← hmc]

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.eq_zero_of_forall_residueField_functional' : ∀ (A M : Type) [CommRing A] [IsReduced A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (x : M), (∀ (p : Ideal A) [p.IsPrime] (l : M →ₗ[A] p.ResidueField), l x = 0) → x = 0 := by
  first | exact @GlobalTheory.eq_zero_of_forall_residueField_functional | exact GlobalTheory.eq_zero_of_forall_residueField_functional | (intros; apply GlobalTheory.eq_zero_of_forall_residueField_functional <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_smul_dvd_of_localization_atPrime_tensor' : ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    (Q : Ideal O) [Q.IsPrime] (b : R) (m : O ⊗[R] C),
    (∃ m' : Localization.AtPrime Q ⊗[R] C,
      (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C m = algebraMap R (Localization.AtPrime Q) b • m') →
    ∃ s ∉ Q, ∃ m' : O ⊗[R] C, s • m = algebraMap R O b • m' := by
  first | (exact @GlobalTheory.exists_smul_dvd_of_localization_atPrime_tensor) | (exact GlobalTheory.exists_smul_dvd_of_localization_atPrime_tensor) | (intros; apply GlobalTheory.exists_smul_dvd_of_localization_atPrime_tensor  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finset_mem_range_localization_away_of_dvd : ∀ (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] (F : Finset (Localization.AtPrime 𝔭)), ∃ s ∉ 𝔭, ∀ (c : R), s ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭, κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) → ∀ x ∈ F, x ∈ κ.range := by
  first | exact @GlobalTheory.finset_mem_range_of_away_dvd | exact GlobalTheory.finset_mem_range_of_away_dvd | (intros; apply GlobalTheory.finset_mem_range_of_away_dvd <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_subalgebra_atPrime_fractions_equiv : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (C : Subalgebra R B), (∀ c ∈ C, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C, s ∉ Q ∧ s * c = 0) → ∃ V : Subalgebra R (Localization.AtPrime Q), (∀ x : Localization.AtPrime Q, x ∈ V ↔ ∃ a ∈ C, ∃ s ∈ C, s ∉ Q ∧ x * algebraMap B (Localization.AtPrime Q) s = algebraMap B (Localization.AtPrime Q) a) ∧ Nonempty (Localization.AtPrime (Q.comap (C.val : C →ₐ[R] B)) ≃ₐ[R] V) := by
  first | exact @GlobalTheory.localization_subalgebra_frac | exact GlobalTheory.localization_subalgebra_frac | (intros; apply GlobalTheory.localization_subalgebra_frac <;> assumption)
end

section


theorem _root_.GlobalTheory.T.localization_away_injective_atPrime_of_dvd : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime], ∃ t ∉ 𝔭, ∀ (c : R), t ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭, κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) → Function.Injective κ := by
  first | exact @GlobalTheory.localization_away_injective_of_dvd | exact GlobalTheory.localization_away_injective_of_dvd | (intros; apply GlobalTheory.localization_away_injective_of_dvd <;> assumption)
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_smul_mem_range_of_surjective_localized_map : ∀ (R A B : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B), Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) → ∀ b : B, ∃ t ∉ p, t • b ∈ ψ.range := by
  exact @GlobalTheory.exists_smul_mem_range_of_surjective_localization_map
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.localization_tensor_map_injective_coker_killed : ∀ (R A B : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B), Function.Injective ψ → ∀ s : R, s ≠ 0 → (∀ b : B, s • b ∈ ψ.range) → Function.Injective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) ∧ algebraMap R (Localization.AtPrime p) s ≠ 0 ∧ ∀ y : Localization.AtPrime p ⊗[R] B, algebraMap R (Localization.AtPrime p) s • y ∈ (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ).range := by
  first | exact @GlobalTheory.localization_map_injective_coker_killed | exact GlobalTheory.localization_map_injective_coker_killed | (intros; apply GlobalTheory.localization_map_injective_coker_killed <;> assumption)
end
