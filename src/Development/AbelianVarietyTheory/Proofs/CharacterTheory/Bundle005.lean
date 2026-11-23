module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem pair_self_of_isIrrChar_algClosed (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G]
    (χ : G → L) (h : IsIrrChar L L χ) : pair χ χ = 1 := by
  classical
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : ρ.IsIrreducible := hρ

  have key := ρ.card_inv_mul_sum_char_mul_char_eq_finrank ρ
  rw [Representation.IsIrreducible.finrank_intertwiningMap_self] at key
  unfold pair
  rw [finsum_eq_sum_of_fintype]
  simp only [hχ, Algebra.algebraMap_self, RingHom.id_apply]
  simpa using key
end GlobalTheory.BI
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

theorem ind_mul_classFun_eq_ind_mul_restrict :
    ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → ℂ) (φ : G → ℂ),
      (∀ g x : G, φ (x⁻¹ * g * x) = φ g) → ind H ψ * φ = ind H (fun h => ψ h * φ h) := by
  intro G _ _ H ψ φ hφ
  funext g
  have key : ∀ x : G, ext0 H (fun h => ψ h * φ h) (x⁻¹ * g * x) = ext0 H ψ (x⁻¹ * g * x) * φ g := by
    intro x
    rw [← hφ g x]
    simp [ext0]
  simp only [Pi.mul_apply, ind]
  simp_rw [key]
  rw [mul_assoc, finsum_mul]

end GlobalTheory.BI
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem pair_eq_zero_of_isIrrChar_ne : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ),
    IsIrrChar ℂ ℂ a → IsIrrChar ℂ ℂ b → a ≠ b → pair a b = 0 := by
  intro G _ _ a b ha hb hab
  obtain ⟨n, ρ, hρ, ha⟩ := ha
  obtain ⟨m, σ, hσ, hb⟩ := hb
  have := hρ
  have := hσ
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have ha' : a = ρ.character := funext fun g => by simp [ha]
  have hb' : b = σ.character := funext fun g => by simp [hb]
  have hne : ¬ Nonempty (Representation.Equiv σ ρ) := by
    rintro ⟨φ⟩
    exact hab (by rw [ha', hb', Representation.char_iso φ])
  have h := Representation.char_orthonormal ρ σ
  rw [if_neg hne] at h
  unfold pair
  rw [finsum_eq_sum_of_fintype, ha', hb']
  simpa using h
end GlobalTheory.BI
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem matrixChar_iff_isChar : ∀ (G : Type) [Group G] (χ : G → ℂ),
    (∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)) ↔
      IsChar ℂ ℂ χ := by
  intro G _ χ
  constructor
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨n, (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom _).comp ρ), fun g => ?_⟩
    rw [hρ g]
    show _ = Representation.character _ g
    rw [Representation.character,
      LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    change _ = (LinearMap.toMatrix' (Matrix.toLin' _)).trace
    rw [LinearMap.toMatrix'_toLin']
    rfl
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨n, Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp ρ.asGroupHom, fun g => ?_⟩
    rw [hρ g]
    show Representation.character _ g = _
    rw [Representation.character,
      LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    rfl

end GlobalTheory.BI
end

section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_linear : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (m : ℕ) (ζ : K) (lam : G →* Lˣ), m ≠ 0 → IsPrimitiveRoot ζ m → (∀ g : G, g ^ m = 1) → IsChar K L (fun g => (lam g : L)) := by
  intro K L _ _ _ G _ m ζ lam hm hζ hG
  haveI : NeZero m := ⟨hm⟩
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hζ' : IsPrimitiveRoot (algebraMap K L ζ) m := hζ.map_of_injective hinj
  have h : ∀ g : G, ∃ x : K, algebraMap K L x = (lam g : L) := by
    intro g
    have h1 : (lam g : L) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hG, map_one, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
    exact ⟨ζ ^ i, by rw [map_pow, hi]⟩
  choose μ hμ using h
  let μ' : G →* K :=
    { toFun := μ
      map_one' := hinj (by rw [hμ]; simp)
      map_mul' := fun a b => hinj (by rw [map_mul (algebraMap K L), hμ, hμ, hμ]; simp) }
  refine ⟨1, ((algebraMap K (Module.End K (Fin 1 → K))).toMonoidHom).comp μ', fun g => ?_⟩
  have : Representation.character (((algebraMap K (Module.End K (Fin 1 → K))).toMonoidHom).comp μ' : Representation K G (Fin 1 → K)) g = μ g := by
    change LinearMap.trace K (Fin 1 → K) (algebraMap K (Module.End K (Fin 1 → K)) (μ g)) = μ g
    rw [Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one]
    simp
  rw [this, hμ]
end GlobalTheory.BI
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory

theorem sum_min_succ_eq_add_card {d : ℕ} (e : Fin d → ℕ) (j : ℕ) :
    ∑ i, min (j + 1) (e i) = ∑ i, min j (e i) + (Finset.univ.filter (fun i => j < e i)).card := by
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> omega

theorem card_gt_eq_card_eq_add_card_gt {d : ℕ} (e : Fin d → ℕ) (j : ℕ) :
    (Finset.univ.filter (fun i => j < e i)).card =
      (Finset.univ.filter (fun i => e i = j + 1)).card +
        (Finset.univ.filter (fun i => j + 1 < e i)).card := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> omega

theorem exists_equiv_of_sum_min_eq : ∀ (d d' : ℕ) (e : Fin d → ℕ) (e' : Fin d' → ℕ),
    (∀ i, 0 < e i) → (∀ i, 0 < e' i) → (∀ j : ℕ, ∑ i, min j (e i) = ∑ i, min j (e' i)) →
    ∃ σ : Fin d ≃ Fin d', ∀ i, e' (σ i) = e i := by
  intro d d' e e' he he' h
  have h1 : ∀ j, (Finset.univ.filter (fun i => j < e i)).card =
      (Finset.univ.filter (fun i => j < e' i)).card := by
    intro j
    have a := sum_min_succ_eq_add_card e j
    have b := sum_min_succ_eq_add_card e' j
    have c := h j
    have c' := h (j + 1)
    omega
  have h2 : ∀ j, Fintype.card {i // e i = j} = Fintype.card {i // e' i = j} := by
    intro j
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rcases j with _ | j
    · rw [Finset.filter_false_of_mem (fun i _ => (he i).ne'),
        Finset.filter_false_of_mem (fun i _ => (he' i).ne')]
      simp
    · have a := card_gt_eq_card_eq_add_card_gt e j
      have b := card_gt_eq_card_eq_add_card_gt e' j
      have c := h1 j
      have c' := h1 (j + 1)
      omega
  exact ⟨Equiv.ofFiberEquiv (f := e) (g := e') (fun j => Fintype.equivOfCardEq (h2 j)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

end GlobalTheory
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.QBinomialSum

lemma prod_succ_succ (x : ℂ) (n a : ℕ) :
    ∏ i ∈ Finset.range (a + 1), (x ^ (n + 1) - x ^ i)
      = (x ^ (n + 1) - 1) * x ^ a * ∏ i ∈ Finset.range a, (x ^ n - x ^ i) := by
  rw [Finset.prod_range_succ']
  have : ∀ i, x ^ (n + 1) - x ^ (i + 1) = x * (x ^ n - x ^ i) := fun i => by ring
  simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  ring

lemma den_ne (x : ℂ) (hx : x ≠ 0) (h1 : ∀ k : ℕ, x ^ (k + 1) - 1 ≠ 0) (a : ℕ) :
    ∏ i ∈ Finset.range a, (x ^ a - x ^ i) ≠ 0 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [prod_succ_succ]
    exact mul_ne_zero (mul_ne_zero (h1 a) (pow_ne_zero _ hx)) ih

lemma sum_eq (x : ℂ) (hx : x ≠ 0) (h1 : ∀ k : ℕ, x ^ (k + 1) - 1 ≠ 0) (n : ℕ) :
    ∑ a ∈ Finset.range n,
      (∏ i ∈ Finset.range (a + 1), (x ^ n - x ^ i)) /
        (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
        ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    set c : ℕ → ℂ := fun a => (∏ i ∈ Finset.range a, (x ^ n - x ^ i)) /
        (∏ i ∈ Finset.range a, (x ^ a - x ^ i)) *
        ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) with hc
    have key : ∀ a, (∏ i ∈ Finset.range (a + 1), (x ^ (n + 1) - x ^ i)) /
        (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
        ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) =
        (∏ i ∈ Finset.range (a + 1), (x ^ n - x ^ i)) /
        (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
        (∏ i ∈ Finset.range a, (1 - x ^ (i + 1))) + (c a - c (a + 1)) := by
      intro a
      simp only [hc]
      rw [prod_succ_succ x n a, prod_succ_succ x a a,
        Finset.prod_range_succ (fun i => x ^ n - x ^ i),
        Finset.prod_range_succ (fun i => 1 - x ^ (i + 1))]
      have hd := den_ne x hx h1 a
      have h2 := h1 a
      have h3 := pow_ne_zero a hx
      generalize ∏ i ∈ Finset.range a, (x ^ a - x ^ i) = D at *
      generalize ∏ i ∈ Finset.range a, (x ^ n - x ^ i) = P at *
      generalize ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) = F at *
      field_simp
      ring
    have hz : ∏ i ∈ Finset.range (n + 1), (x ^ n - x ^ i) = 0 :=
      Finset.prod_eq_zero (Finset.self_mem_range_succ n) (sub_self _)
    simp only [key]
    rw [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_range_succ, ih, hz]
    have h0 : c 0 = 1 := by simp [hc]
    have hn : c (n + 1) = 0 := by simp only [hc, hz]; simp
    rw [h0, hn]
    push_cast
    simp

theorem sum_gaussian_mul_prod : ∀ (q n : ℕ) (N : ℕ → ℕ), 2 ≤ q → (∀ a, a ≤ n → N a * ∏ i ∈ Finset.range a, (q ^ a - q ^ i) = ∏ i ∈ Finset.range a, (q ^ n - q ^ i)) → ∑ a ∈ Finset.Icc 1 n, (N a : ℂ) * ∏ i ∈ Finset.Ico 1 a, (1 - (q : ℂ) ^ i) = n := by
  intro q n N hq hN
  have hx : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h1 : ∀ k : ℕ, (q : ℂ) ^ (k + 1) - 1 ≠ 0 := by
    intro k h
    have h' : (q : ℂ) ^ (k + 1) = 1 := sub_eq_zero.mp h
    have h'' : q ^ (k + 1) = 1 := by exact_mod_cast h'
    have := Nat.one_lt_pow (n := k + 1) (a := q) (by omega) (by omega)
    omega
  have cast : ∀ m a, a ≤ m → ((∏ i ∈ Finset.range a, (q ^ m - q ^ i) : ℕ) : ℂ)
      = ∏ i ∈ Finset.range a, ((q : ℂ) ^ m - (q : ℂ) ^ i) := by
    intro m a ha
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) (by omega))]
    push_cast
    rfl
  rw [← sum_eq (q : ℂ) hx h1 n, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := Finset.mem_range.mp ha
  rw [Finset.prod_Ico_eq_prod_range, add_comm 1 a]
  simp only [Nat.add_sub_cancel]
  have h := congrArg (Nat.cast : ℕ → ℂ) (hN (a + 1) (by omega))
  rw [Nat.cast_mul, cast _ _ le_rfl, cast _ _ (by omega)] at h
  rw [← h, mul_div_cancel_right₀ _ (den_ne _ hx h1 (a + 1))]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [add_comm]

end GlobalTheory.QBinomialSum
end

section


theorem _root_.GlobalTheory.T.one_mem_of_mul_mem_of_forall_prime_exists_not_dvd : ∀ (X : Type) [Finite X] (S : AddSubgroup (X → ℤ)), (∀ f ∈ S, ∀ g ∈ S, f * g ∈ S) → (∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) → (1 : X → ℤ) ∈ S := by
  first | exact @GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd | exact GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd | (intros; apply GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd <;> assumption)
end
